-- | This module implements the desugaring pass which replaces do-notation statements with
-- appropriate calls to bind.

{-# LANGUAGE PatternGuards #-}

module Language.PureScript.Sugar.DoNotation (desugarDoModule) where

import           Prelude.Compat

import           Control.Applicative ((<|>))
import           Control.Monad.Error.Class (MonadError(..))
import           Control.Monad.Supply.Class
import           Control.Monad.Writer.Strict (tell, lift, WriterT(..))
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid (First(..))
import           Language.PureScript.AST
import           Language.PureScript.Crash
import           Language.PureScript.Errors
import           Language.PureScript.Names
import qualified Language.PureScript.Constants.Prelude as C
import           Language.PureScript.PSString (mkString)

-- | Replace all @DoNotationBind@ and @DoNotationValue@ constructors with
-- applications of the bind function in scope, and all @DoNotationLet@
-- constructors with let expressions.
desugarDoModule :: forall m. (MonadSupply m, MonadError MultipleErrors m) => Module -> m Module
desugarDoModule (Module ss coms mn ds exts) = Module ss coms mn <$> parU ds desugarDo <*> pure exts

-- | Desugar a single do statement
desugarDo :: forall m. (MonadSupply m, MonadError MultipleErrors m) => Declaration -> m Declaration
desugarDo d =
  let ss = declSourceSpan d
      (f, _, _) = everywhereOnValuesM return (replace ss) return
  in rethrowWithPosition ss $ f d
  where
  bind :: SourceSpan -> Maybe ModuleName -> Expr
  bind ss m = Var ss (Qualified m (Ident C.bind))

  discard :: SourceSpan -> Maybe ModuleName -> Expr
  discard ss m = Var ss (Qualified m (Ident C.discard))

  fixM :: SourceSpan -> Maybe ModuleName -> Expr
  fixM ss m = Var ss (Qualified m (Ident C.fixM))

  pure' :: SourceSpan -> Maybe ModuleName -> Expr
  pure' ss m = Var ss (Qualified m (Ident C.pure'))

  replace :: SourceSpan -> Expr -> m Expr
  replace pos (Do m els) = go pos m els
  replace _ (PositionedValue pos com v) = PositionedValue pos com <$> rethrowWithPosition pos (replace pos v)
  replace _ other = return other

  stripPositionedBinder :: Binder -> (Maybe SourceSpan, Binder)
  stripPositionedBinder (PositionedBinder ss _ b) =
    let (ss', b') = stripPositionedBinder b
     in (ss' <|> Just ss, b')
  stripPositionedBinder b =
    (Nothing, b)

  go :: SourceSpan -> Maybe ModuleName -> [DoNotationElement] -> m Expr
  go _ _ [] = internalError "The impossible happened in desugarDo"
  go _ _ [DoNotationValue val] = return val
  go pos m (DoNotationValue val : rest) = do
    rest' <- go pos m rest
    return $ App (App (discard pos m) val) (Abs (VarBinder pos UnusedIdent) rest')
  go _ _ [DoNotationBind _ _] = throwError . errorMessage $ InvalidDoBind
  go _ _ (DoNotationBind b _ : _) | First (Just ident) <- foldMap fromIdent (binderNames b) =
      throwError . errorMessage $ CannotUseBindWithDo (Ident ident)
    where
      fromIdent (Ident i) | i `elem` [ C.bind, C.discard ] = First (Just i)
      fromIdent _ = mempty
  go pos m (DoNotationBind binder val : rest) = do
    rest' <- go pos m rest
    let (mss, binder') = stripPositionedBinder binder
    let ss = fromMaybe pos mss
    case binder' of
      NullBinder ->
        return $ App (App (bind pos m) val) (Abs (VarBinder ss UnusedIdent) rest')
      VarBinder _ ident ->
        return $ App (App (bind pos m) val) (Abs (VarBinder ss ident) rest')
      _ -> do
        ident <- freshIdent'
        return $ App (App (bind pos m) val) (Abs (VarBinder pos ident) (Case [Var pos (Qualified Nothing ident)] [CaseAlternative [binder] [MkUnguarded rest']]))
  go _ _ [DoNotationLet _] = throwError . errorMessage $ InvalidDoLet
  go pos m (DoNotationLet ds : rest) = do
    let checkBind :: Declaration -> m ()
        checkBind (ValueDecl (ss, _) i@(Ident name) _ _ _)
          | name `elem` [ C.bind, C.discard ] = throwError . errorMessage' ss $ CannotUseBindWithDo i
        checkBind _ = pure ()
    mapM_ checkBind ds
    rest' <- go pos m rest
    return $ Let FromLet ds rest'
  go _ _ [DoNotationRec _] = throwError . errorMessage $ InvalidDoRec
  go pos m (DoNotationRec stmts : rest) = do
    (newStmts, (origNames, substNames)) <- untieDoRec stmts
    let inputObj = LiteralBinder pos $ ObjectLiteral $
          zip (mkString . showIdent <$> origNames) (VarBinder pos <$> origNames)
        outputObj = zip (mkString . showIdent <$> origNames) (Var pos . Qualified Nothing <$> substNames)
    fixedStmts <- go pos m $ newStmts ++ [DoNotationValue $ App (pure' pos m) $ Literal pos $ ObjectLiteral outputObj]
    go pos m $ DoNotationBind inputObj (App (fixM pos m) $ Abs inputObj fixedStmts) : rest

  go _ m (PositionedDoNotationElement pos com el : rest) = rethrowWithPosition pos $ PositionedValue pos com <$> go pos m (el : rest)

  untieDoRec :: [DoNotationElement] -> m ([DoNotationElement], ([Ident], [Ident]))
  untieDoRec = runWriterT . traverse untie where
    untie = \case
      DoNotationBind b e -> do
        let origNames = binderNames b
        substNames <- traverse (fmap lift freshIdent . showIdent) origNames
        tell (origNames, substNames)
        pure $ DoNotationBind (renameBinderNames (M.fromList $ zip origNames substNames) b) e
      PositionedDoNotationElement pos com el -> PositionedDoNotationElement pos com <$> untie el
      s -> pure s
    renameBinderNames m = onBinder where
      (_, _, onBinder) = everywhereOnValues id id $ \case
        NamedBinder ss i b ->
          NamedBinder ss (substitute m i) b
        VarBinder ss i ->
          VarBinder ss $ substitute m i
        s -> s
      substitute ss i = fromMaybe i $ M.lookup i ss
