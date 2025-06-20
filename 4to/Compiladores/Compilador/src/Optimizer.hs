{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Optimizer where
import MonadFD4 ( MonadFD4, lookupDecl, failFD4 )
import Lang ( Tm(..), TTerm, Decl (declBody, Decl), Const (..), BinaryOp (..), Var (..), Name, getTy, Scope (Sc1), Scope2 (Sc2) )
import Subst
import Eval ( semOp )
import PPrint ( ppName, freshen )
import Helper ( hasEffects, getUsedVarsNames )
import Control.Monad (filterM )

-- | Max optimization iterations
maxIt :: Int
maxIt = 10

-- | Optimize a single declaration
optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize d = do
    oBody <- optimize' maxIt (declBody d)
    return $ d { declBody = oBody }

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' i t = constantFolding t >>= constantPropagation [] >>= inlineExpansion >>= optimize' (i - 1)

-- | Constant Folding
constantFolding :: MonadFD4 m => TTerm ->  m TTerm
constantFolding v@(V _ _) = return v
constantFolding c@(Const _ _) = return c
constantFolding (Lam i n ty (Sc1 t)) = do
    t' <- constantFolding t
    return $ Lam i n ty (close n t')
constantFolding (App i t1 t2) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return $ App i t1' t2'
constantFolding (Print i s t) = do
    t' <- constantFolding t
    return $ Print i s t'
constantFolding (Fix i n1 ty1 n2 ty2 (Sc2 t)) = do
    t' <- constantFolding t
    return $ Fix i n1 ty1 n2 ty2 (close2 n1 n2 t')
constantFolding (IfZ i t1 t2 t3) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    t3' <- constantFolding t3
    return $ IfZ i t1' t2' t3'
constantFolding (Let i n ty t1 (Sc1 t2)) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return $ Let i n ty t1' (close n t2')
constantFolding (BinaryOp i op (Const _ (CNat n1)) (Const _ (CNat n2))) =
    return $ Const i (CNat (semOp op n1 n2))
constantFolding (BinaryOp i Add t (Const _ (CNat 0))) = return t
constantFolding (BinaryOp i Add (Const _ (CNat 0)) t) = return t
constantFolding (BinaryOp i Sub t (Const _ (CNat 0))) = return t
constantFolding b@(BinaryOp _ Sub (Const i (CNat 0)) t) = do
    he <- hasEffects t
    if he then return b else return $ Const i (CNat 0)
constantFolding t = return t

-- | Constant Propagation
constantPropagation :: MonadFD4 m => [(Name, TTerm)] -> TTerm -> m TTerm
constantPropagation _ v@(V i (Global n)) = do
  mtm <- lookupDecl n
  case mtm of
    Nothing -> failFD4 $ "Error en optimizacion (CP): variable no declarada: " ++ ppName n
    Just c@(Const {}) -> return c
    Just _ -> return v
constantPropagation env v@(V i (Free n)) =
  case lookup n env of
    Nothing -> return v
    Just t -> return t
constantPropagation _ v@(V i (Bound n)) = return v
constantPropagation _ c@(Const _ _) = return c
constantPropagation env (Lam i n ty (Sc1 t)) = do
  t' <- constantPropagation env t
  return $ Lam i n ty (close n t')
constantPropagation env (App i t1 t2) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  return $ App i t1' t2'
constantPropagation env (Print i s t) = do
  t' <- constantPropagation env t
  return $ Print i s t'
constantPropagation env (BinaryOp i op t1 t2) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  return $ BinaryOp i op t1' t2'
constantPropagation env (Fix i n1 ty1 n2 ty2 (Sc2 t)) = do
  t' <- constantPropagation env t
  return $ Fix i n1 ty2 n2 ty2 (close2 n1 n2 t')
constantPropagation env (IfZ i t1 t2 t3) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  t3' <- constantPropagation env t3
  return $ IfZ i t1' t2' t3'
constantPropagation env (Let i n ty t1 (Sc1 t2)) = do
  t1' <- constantPropagation env t1
  case t1' of
    c@(Const _ v) -> constantPropagation ((n, c):env) (open n (Sc1 t2))
    _ -> do
      scope' <- constantPropagation env t2
      return $ Let i n ty t1' (close n scope')

-- | Inline Expansion
inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion t = inlineExpansion' (getUsedVarsNames t) [] t

inlineExpansion' :: MonadFD4 m => [Name] -> [(Name, TTerm)] -> TTerm -> m TTerm
inlineExpansion' _ _ v@(V _ _) = return v
inlineExpansion' _ _ c@(Const _ _) = return c
inlineExpansion' nms env (Lam i n ty (Sc1 t)) = do
  t' <- inlineExpansion' nms env t
  return $ Lam i n ty (Sc1 t')
inlineExpansion' nms env (Print i s t) = do
  t' <- inlineExpansion' nms env t
  return $ Print i s t'
inlineExpansion' nms env (BinaryOp i op t1 t2) = do
  t1' <- inlineExpansion' nms env t1
  t2' <- inlineExpansion' nms env t2
  return $ BinaryOp i op t1' t2'
inlineExpansion' nms env (Fix i n1 ty1 n2 ty2 (Sc2 t)) = do
  t' <- inlineExpansion' nms env t
  return $ Fix i n1 ty1 n2 ty2 (Sc2 t')
inlineExpansion' nms env (IfZ i t1 t2 t3) = do
  t1' <- inlineExpansion' nms env t1
  t2' <- inlineExpansion' nms env t2
  t3' <- inlineExpansion' nms env t3
  return $ IfZ i t1' t2' t3'
inlineExpansion' nms env (Let i n ty t1 (Sc1 t2)) = do
  t1' <- inlineExpansion' nms env t1
  t2' <- inlineExpansion' nms ((n ,t1'):env) t2
  return $ Let i n ty t1' (Sc1 t2')
inlineExpansion' nms env t@(App _ f@(Lam i n ty sc) c@(Const {})) = return $ subst c sc
-- Se asume que la variable es siempre funcion
inlineExpansion' nms env t@(App _ (V _ (Bound i)) c@(Const {})) = return t
-- Caso Aplicacion con t' complejo
inlineExpansion' nms env (App i (V _ (Free n)) t') = do
  case lookup n env of
    Nothing -> failFD4 $ "Error en optimizacion (IE): variable libre no declarada: " ++ ppName n
    Just t -> inlineExpansion' nms env (App i t t')
inlineExpansion' nms env (App i (V _ (Global f)) t') = do
  mtm <- lookupDecl f
  case mtm of
    Nothing -> failFD4 $ "Error en optimizacion (IE): variable no declarada: " ++ ppName f
    Just t -> inlineExpansion' nms env (App i t t')
inlineExpansion' nms env t@(App i (Lam _ _ _ scope) t') =
  let z = freshen nms "x"
  in return $ Let i z (getTy t') t' scope
inlineExpansion' nms env (App i t1 t2) = do
  t1' <- inlineExpansion' nms env t1
  t2' <- inlineExpansion' nms env t2
  return $ App i t1' t2'

-- | Dead code elimination
deadCodeElimination :: MonadFD4 m => [Decl TTerm] -> m [Decl TTerm]
deadCodeElimination [] = return []
deadCodeElimination ds = do
  decls <- mapM (addReferences . declBody) ds
  let cdecls = concat decls
  filterM (hasEffects . declBody) ds

-- | Devuelve declaraciones referenciadas
addReferences :: MonadFD4 m => TTerm -> m [Decl TTerm]
addReferences (V (p, ty) (Global n)) = do
  mtm <- lookupDecl n
  case mtm of
    Nothing -> failFD4 $ "Error en optimizacion (DCE): variable no declarada: " ++ ppName n
    Just t -> return [Decl p n ty t]
addReferences (Lam _ _ _ (Sc1 t)) = addReferences t
addReferences (App _ t1 t2) = do
  r1 <- addReferences t1
  r2 <- addReferences t2
  return $ r1 ++ r2
addReferences (Print _ _ t) = addReferences t
addReferences (BinaryOp _ _ t1 t2) = do
  r1 <- addReferences t1
  r2 <- addReferences t2
  return $ r1 ++ r2
addReferences (Fix _ _ _ _ _ (Sc2 t)) = addReferences t
addReferences (IfZ _ t1 t2 t3) = do
  r1 <- addReferences t1
  r2 <- addReferences t2
  r3 <- addReferences t3
  return $ r1 ++ r2 ++ r3
addReferences (Let _ _ _ t1 (Sc1 t2)) = do
  r1 <- addReferences t1
  r2 <- addReferences t2
  return $ r1 ++ r2
addReferences _ = return []
