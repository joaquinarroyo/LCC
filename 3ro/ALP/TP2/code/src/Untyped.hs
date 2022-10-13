module Untyped where

import           Control.Monad
import           Data.List
import           Data.Maybe

import           Common

----------------------------------------------
-- Seccón 2  
-- Ejercicio 2: Conversión a términos localmente sin nombres
----------------------------------------------

conversion :: LamTerm -> Term
conversion t = conversionAux t []

conversionAux :: LamTerm -> [String] -> Term
conversionAux (LVar s) l = case index s l of
                            Just n  -> Bound n
                            Nothing -> Free (Global s)
conversionAux (App t1 t2) l = conversionAux t1 l :@: conversionAux t2 l
conversionAux (Abs s t) l = Lam (conversionAux t (s:l))

index :: String -> [String] -> Maybe Int
index s [] = Nothing
index s (x:xs) | s == x = Just 0
               | otherwise = case index s xs of
                                Just n  -> Just (1 + n)
                                Nothing -> Nothing

-------------------------------
-- Sección 3
-------------------------------

-- Ejercicio 3
vapp :: Value -> Value -> Value
vapp (VLam lam) val         = lam val
vapp (VNeutral neutral) val = VNeutral (NApp neutral val)

-- Ejercicio 4
eval :: NameEnv Value -> Term -> Value
eval e t = eval' t (e, [])

eval' :: Term -> (NameEnv Value, [Value]) -> Value
-- Variable capturada
eval' (Bound ii) (_, lEnv) = lEnv !! ii
-- Es una variable libre de la cual podemos o no conocer su valor en el entorno
-- podemos intentar remplazar por la conocida
eval' (Free name) (gEnv, lEnv) = globalSolver name gEnv
-- Componemos t1 y t2
eval' (t1 :@: t2)  state       = vapp (eval' t1  state) (eval' t2  state)
-- Definimos una nueva funcion, quedamos a la espera de un valor para la variable
-- ligada a este lambda 
eval' (Lam term)  (gEnv, lEnv) = VLam (\ x -> eval' term (gEnv, x:lEnv))

-- Resulve el nombre de funciones conocidas
globalSolver :: Name -> NameEnv Value -> Value
-- La funcion no es conocida
globalSolver name [] = VNeutral (NFree name)
-- Caso general: 1) si conozco a la funcion la devulvo; 2) sigo buscando entre las conocidas
globalSolver name ((name', value):es) | name == name' = value
                                      | otherwise     = globalSolver name es

--------------------------------
-- Sección 4 - Mostrando Valores
--------------------------------

-- Ejercicio 5
quote :: Value -> Term
quote = quote' 0

quote' :: Int -> Value -> Term
quote' i (VLam f) = Lam (quote'' (i+1) (f (VNeutral (NFree (Quote i)))))
quote' i (VNeutral (NFree n)) = Free n
quote' i (VNeutral (NApp var1 var2)) = (quote' i (VNeutral var1)) :@: (quote' i var2)

quote'' :: Int -> Value -> Term
quote'' i v@(VLam f) = quote' i v
quote'' i (VNeutral (NFree g@(Global s))) = Free g
quote'' i (VNeutral (NFree (Quote k))) = Bound (i - k - 1)
quote'' i (VNeutral (NApp var1 var2)) = (quote'' i (VNeutral var1)) :@: (quote'' i var2)