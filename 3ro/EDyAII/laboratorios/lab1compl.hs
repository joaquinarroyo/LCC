module Lab1C where

import Data.List
import Data.Ord
import Data.Function

type Texto = String

{-
   Definir una función que dado un caracter y un texto calcule la frecuencia 
   con la que ocurre el caracter en el texto
   Por ejemplo: frecuency 'a' "casa" = 0.5 
-}

foo :: Int -> Int -> Float
foo a b = fromIntegral a / fromIntegral b

countChar:: Char -> Texto -> Int
countChar c [] = 0
countChar c (x:xs) | c == x = 1 + countChar c xs
                   | otherwise = countChar c xs

frecuency :: Char -> Texto -> Float
frecuency c text = foo (countChar c text) (length text)

{-                      
  Definir una función frecuencyMap que dado un texto calcule la frecuencia 
  con la que ocurre cada caracter del texto en éste.
  La lista resultado debe estar ordenada respecto a la frecuencia con la que ocurre 
  cada caracter, de menor a mayor frecuencia. 
    
  Por ejemplo: frecuencyMap "casa" = [('c',0.25),('s',0.25),('a',0.5)]

-}

deleteDuplicate :: (Eq a) => [a] -> [a]
deleteDuplicate [] = []
deleteDuplicate (x:xs) = x : deleteDuplicate (filter (/= x) xs)

ssort :: Ord t => [(Char, t)] -> [(Char, t)]
ssort = sortBy (compare `on` snd)

frecuencyMapAux :: Texto -> Texto -> [(Char, Float)]
frecuencyMapAux [] _ = []
frecuencyMapAux (x:xs) text = (x, frecuency x text) : frecuencyMapAux xs text

frecuencyMap :: Texto -> [(Char, Float)]
frecuencyMap [] = []
frecuencyMap text = ssort list
    where
        list = deleteDuplicate (frecuencyMapAux text text)

{-
  Definir una función subconjuntos, que dada una lista xs devuelva una lista 
  con las listas que pueden generarse con los elementos de xs.

  Por ejemplo: subconjuntos [2,3,4] = [[2,3,4],[2,3],[2,4],[2],[3,4],[3],[4],[]]
-}

subconjuntos :: Eq a => [a] -> [[a]]
subconjuntos [] = [[]]
subconjuntos (x:xs) = map (x:) (subconjuntos xs) ++ subconjuntos xs

{-
 Definir una función intercala :: a -> [a] -> [[a]]
 tal que (intercala x ys) contiene las listas que se obtienen
 intercalando x entre los elementos de ys. 
 
 Por ejemplo: intercala 1 [2,3]  ==  [[1,2,3],[2,1,3],[2,3,1]]
-}

intercalaAux :: a -> [a] -> Int -> [[a]]
intercalaAux n list i | i <= length list = (take i list ++ [n] ++ drop i list) : intercalaAux n list (i+1)
                      | otherwise = []

intercala :: a -> [a] -> [[a]]
intercala n list = intercalaAux n list 0

{- 
  Definir una función permutaciones que dada una lista calcule todas las permutaciones
  posibles de sus elementos. Ayuda: la función anterior puede ser útil. 

  Por ejemplo: permutaciones "abc" = ["abc","bac","cba","bca","cab","acb"]
-}

permutacionesAux :: [a] -> Int -> [[[a]]]
permutacionesAux [] _ = []
permutacionesAux (x:xs) i | i < length (x:xs) = intercala x xs : permutacionesAux (xs++[x]) (i+1)
                          | otherwise = []

permutaciones :: Eq a => [a] -> [[a]]
permutaciones [] = []
permutaciones list = deleteDuplicate (concat (permutacionesAux list 0))






