module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b (LVar n    ) = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (LApp t u  ) = conversion' b t :@: conversion' b u
conversion' b (LAbs n t u) = Lam t (conversion' (n:b) u)
-- Ej 02
conversion' b (LLet s t1 t2) = Let (conversion' b t1) (conversion' (s:b) t2)
-- Ej 03
conversion' b (LAs t ty) = As (conversion' b t) ty
-- Ej 05
conversion' b LUnit = Unit
-- Ej 07
conversion' b (LFst t) = Fst (conversion' b t)
conversion' b (LSnd t) = Snd (conversion' b t)
conversion' b (LPair t1 t2) = Pair (conversion' b t1) (conversion' b t2)
-- Ej 09
conversion' b LZero = Zero
conversion' b (LSuc t) = Suc (conversion' b t)
conversion' b (LRec t1 t2 t3) = Rec (conversion' b t1) (conversion' b t2) (conversion' b t3)

-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i+1) t u)
-- Ej 02
sub i t (Let t1 t2)           = Let (sub i t t1) (sub (i+1) t t2)
-- Ej 03
sub i t (As t' ty) = As (sub i t t') ty
-- Ej 05
sub i t Unit = Unit
-- Ej 07
sub i t (Fst t') = Fst (sub i t t')
sub i t (Snd t') = Snd (sub i t t')
sub i t (Pair t1 t2) = Pair (sub i t t1) (sub i t t2)
-- Ej 09
sub i t Zero = Zero
sub i t (Suc t') = Suc (sub i t t')
sub i t (Rec t1 t2 t3) = Rec (sub i t t1) (sub i t t2) (sub i t t3)

-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound _             ) = error "variable ligada inesperada en eval"
eval e (Free  n             ) = fst $ fromJust $ lookup n e
eval _ (Lam      t   u      ) = VLam t u
eval e (Lam _ u  :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam t u1 :@: u2) = let v2 = eval e u2 in eval e (sub 0 (quote v2) u1)
eval e (u        :@: v      ) = case eval e u of
  VLam t u' -> eval e (Lam t u' :@: v)
  _         -> error "Error de tipo en run-time, verificar type checker"
-- Ej 02
eval e (Let t1 t2) = eval e (sub 0 t1 t2)
-- Ej 03
eval e (As t _) = eval e t
-- Ej 05
eval e Unit = VUnit
-- Ej 06
{-
Estas dos definiciones se agregaron por tema de optimizacion 
pero no son necesarias, ya que las siguientes cubren todos los casos.
-}
eval e (Fst (Pair t1 _)) = eval e t1
eval e (Snd (Pair _ t2)) = eval e t2
-------
eval e (Fst t) = case eval e t of
                  VPair v1 _ -> v1
                  _ -> error "Error de tipo en run-time"
eval e (Snd t) = case eval e t of
                  VPair _ v2 -> v2
                  _ -> error "Error de tipo en run-time"
eval e (Pair t1 t2) = let v = eval e t1
                      in VPair v (eval e t2)
-- Ej 09
eval e Zero = VNum NZero
eval e (Suc t) = case eval e t of
                  VNum x -> VNum (NSuc x)
                  _      -> error "Error de tipo en run-time"
eval e (Rec t1 t2 Zero) = eval e t1
eval e (Rec t1 t2 (Suc t)) = eval e ((t2 :@: (Rec t1 t2 t) :@: t))
eval e (Rec t1 t2 t3) = let v = eval e t3
                        in eval e (Rec t1 t2 (quote v))


-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f) = Lam t f
-- Ej 05
quote VUnit = Unit
-- Ej 06
quote (VPair v1 v2) = Pair (quote v1) (quote v2)
-- Ej 09
quote (VNum NZero) = Zero
quote (VNum (NSuc v)) = Suc (quote (VNum v))


-----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error
matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

notPairError :: Type -> Either String Type
notPairError t1 = err $ render (printType t1) ++ " no es una tupla."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
-- Ej 02
infer' c e (Let t1 t2) = infer' c e t1 >>= 
                         \ty -> infer' (ty:c) e t2 >>=
                         \ty'-> ret ty'
-- Ej 03
infer' c e (As t ty) = infer' c e t >>=
                       \ty' -> if ty /= ty' then matchError ty ty' else ret ty
-- Ej 06
infer' c e Unit = ret UnitT
infer' c e (Fst t) = infer' c e t >>=
                     \ty -> case ty of
                             PairT t1 _ -> ret t1
                             t'         -> notPairError t'
infer' c e (Snd t) = infer' c e t >>=
                     \ty -> case ty of
                             PairT _ t2 -> ret t2
                             t'         -> notPairError t'
infer' c e (Pair t1 t2) = infer' c e t1 >>=
                          \ty1 -> infer' c e t2 >>=
                          \ty2 -> ret (PairT ty1 ty2)
-- Ej 09
infer' c e Zero = ret NatT
infer' c e (Suc t) = infer' c e t >>=
                     \ty -> if ty /= NatT then matchError NatT ty else ret NatT
infer' c e (Rec t1 t2 t3) = infer' c e t1 >>=
                            \ty1 -> infer' c e t2 >>= 
                            \ty2 -> if ty2 /= (FunT ty1 (FunT NatT ty1)) 
                                    then matchError (FunT ty1 (FunT NatT ty1)) ty2
                                    else infer' c e t3 >>= \ty3 -> if ty3 /= NatT
                                                                   then matchError NatT ty3
                                                                   else ret ty1
----------------------------------
