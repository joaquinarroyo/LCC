{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Helper where

import Lang
import Common
import MonadFD4
import Subst ( open, open2 )

-- | Transforma bindings a tipos
bindingToType :: [(Name, Ty)] -> Ty -> Ty
bindingToType [(_, t)] ty     = FunTy t ty Nothing
bindingToType ((_, t):bs) ty  = FunTy t (bindingToType bs ty) Nothing

-- | Chequea que un tipo (sinonimo) este definido
checkSin :: MonadFD4 m => Pos -> Ty -> m Ty
checkSin p (SynTy n)      = do
  mty <- lookupSinTy n
  case mty of
    Nothing -> failPosFD4 p "Type synonym not declared"
    Just ty -> return ty
checkSin p (FunTy a b n)  = do
  a' <- checkSin p a
  b' <- checkSin p b
  return $ FunTy a' b' n
checkSin _ ty             = return ty

-- | Chequea que una lista de tipos (sinonimos) esten definidos
checkSins :: MonadFD4 m => Pos -> [(Name, Ty)] -> m [(Name, Ty)]
checkSins p [(v, vty)]    = do
  vty' <- checkSin p vty
  return [(v, vty')]
checkSins p ((v, vty):vs) = do
  vty' <- checkSin p vty
  vs' <- checkSins p vs
  return $ (v, vty') : vs'

-- | Chequea si un termino tiene efectos secundarios
hasEffects :: MonadFD4 m => TTerm -> m Bool
hasEffects (V i (Global n)) = do
  mt <- lookupDecl n
  case mt of
    Nothing -> return False
    Just t  -> hasEffects t
hasEffects (V _ _) = return False
hasEffects (Const _ _) = return False
hasEffects (Lam _ n _ scope) = hasEffects (open n scope)
hasEffects (App _ t1 t2) = do
  b1 <- hasEffects t1
  b2 <- hasEffects t2
  return $ b1 || b2
hasEffects (Print {}) = return True
hasEffects (BinaryOp i op t1 t2) = do
  b1 <- hasEffects t1
  b2 <- hasEffects t2
  return $ b1 || b2
hasEffects (Fix _ n1 _ n2 _ scope) = hasEffects (open2 n1 n2 scope)
hasEffects (IfZ i t1 t2 t3) = do
  b1 <- hasEffects t1
  b2 <- hasEffects t2
  b3 <- hasEffects t3
  return $ b1 || b2 || b3
hasEffects (Let i n ty t1 scope) = do
  b1 <- hasEffects t1
  b2 <- hasEffects (open n scope)
  return $ b1 || b2

-- | Obtiene los nombres de variable usados en un termino
getUsedVarsNames :: TTerm -> [Name]
getUsedVarsNames (V _ (Free n)) = [n]
getUsedVarsNames (V _ (Global n)) = [n]
getUsedVarsNames (V _ _) = []
getUsedVarsNames (Const _ _) = []
getUsedVarsNames (App _ t1 t2) =
  let
    (n1, n2) = (getUsedVarsNames t1, getUsedVarsNames t2)
  in n1 ++ n2
getUsedVarsNames (Print _ _ t) = getUsedVarsNames t
getUsedVarsNames (BinaryOp _ _ t1 t2) =
  let
    (n1, n2) = (getUsedVarsNames t1, getUsedVarsNames t2)
  in n1 ++ n2
getUsedVarsNames (Fix _ n1 _ n2 _ scope) = getUsedVarsNames (open2 n1 n2 scope)
getUsedVarsNames (IfZ _ t1 t2 t3) =
  let
    (n1, n2, n3) = (getUsedVarsNames t1, getUsedVarsNames t2, getUsedVarsNames t3)
  in n1 ++ n2 ++ n3
getUsedVarsNames (Let i n ty t scope) =
  let
    (n1, n2) = (getUsedVarsNames t, getUsedVarsNames (open n scope))
  in n1 ++ n2
getUsedVarsNames _ = []