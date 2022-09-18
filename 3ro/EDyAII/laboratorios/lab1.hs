{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
{-# HLINT ignore "Use list literal" #-}
{-# HLINT ignore "Use if" #-}
{-# HLINT ignore "Use minimum" #-}
{-# HLINT ignore "Use map" #-}
module Lab01 where

import Data.List
import GHC.IO.Encoding.Iconv (localeEncodingName)
import Data.Char (isDigit, ord)


{-
1) Corregir los siguientes programas de modo que sean aceptados por GHCi.
-}

-- -- a)
-- not :: Bool -> Bool
-- not b = case b of
--         True -> False
--         False -> True

-- -- b)
in2 :: [a] -> [a]
in2 []          =  error "empty list"
in2 [x]         =  []
in2 (x:xs)      =  x : in2 xs

-- c)
length2 :: [a] -> Int
length2 []        =  0
length2 (x:xs)     =  1 + length2 xs

-- -- d)
list123 :: [Integer]
list123 = 1 : (2 : (3 : []))

-- -- e) 
(++!) :: [a] -> [a] -> [a]
[]     ++! ys = ys
(x:xs) ++! ys = x : xs ++! ys

-- -- f)
addToTail :: Num a => a -> [a] -> [a]
addToTail x xs = map (+x) (tail xs)

-- -- g)
listmin :: Ord a1 => [a1] -> a1
listmin xs = head (sort xs)

-- -- h)
smap :: (t -> a) -> [t] -> [a]
smap f [] = []
smap f [x] = [f x]
smap f (x:xs) = f x : smap f xs


-- 2. Definir las siguientes funciones y determinar su tipo:

-- a) five, que dado cualquier valor, devuelve 5
five :: a -> Int
five x = 5

-- b) apply, que toma una función y un valor, y devuelve el resultado de
-- aplicar la función al valor dado
apply :: (a -> b) -> a -> b
apply f = f

-- c) ident, la función identidad
ident :: a -> a
ident x = x

-- d) first, que toma un par ordenado, y devuelve su primera componente
first :: (a, b) -> a
first (x, _) = x

-- -- e) derive, que aproxima la derivada de una función dada en un punto dado
derive :: (Float -> Float) -> Float -> Float
derive f x =  (f (x + h) - f x)/h
        where h = 0.0000001

-- f) sign, la función signo
sign :: Int -> Int
sign x  | x > 0 = 1
        | x < 0 = -1
        | otherwise = 0

-- g) vabs, la función valor absoluto (usando sign y sin usarla)
vabs1 :: Int -> Int
vabs1 x = sign x * x

vabs2 :: Int -> Int
vabs2 x = if x < 0 then -x else x

-- h) pot, que toma un entero y un número, y devuelve el resultado de
-- elevar el segundo a la potencia dada por el primero
pot :: Int -> Float -> Float
pot 0 y = 1
pot x y = y * pot (x-1) y

-- i) xor, el operador de disyunción exclusiva
xor :: Bool -> Bool -> Bool
xor a b | a == b = False
        | otherwise = True

-- j) max3, que toma tres números enteros y devuelve el máximo entre llos
max3 :: Int -> Int -> Int -> Int
max3 x y z = max z (max x y)

-- k) swap, que toma un par y devuelve el par con sus componentes invertidas
swap :: (a, b) -> (b, a)
swap (a, b) = (b, a)

{- 
3) Definir una función que determine si un año es bisiesto o no, de
acuerdo a la siguiente definición:

año bisiesto 1. m. El que tiene un día más que el año común, añadido al mes de febrero. Se repite
cada cuatro años, a excepción del último de cada siglo cuyo número de centenas no sea múltiplo
de cuatro. (Diccionario de la Real Academia Espaola, 22ª ed.)

¿Cuál es el tipo de la función definida?
-}

esBisiesto :: Int -> Bool
esBisiesto x = mod x 4 == 0 && mod x 100 == 0 && mod x 400 == 0

{-
4)

Defina un operador infijo *$ que implemente la multiplicación de un
vector por un escalar. Representaremos a los vectores mediante listas
de Haskell. Así, dada una lista ns y un número n, el valor ns *$ n
debe ser igual a la lista ns con todos sus elementos multiplicados por
n. Por ejemplo,

[ 2, 3 ] *$ 5 == [ 10 , 15 ].

El operador *$ debe definirse de manera que la siguiente
expresión sea válida:

-}

(*$) :: [Int] -> Int -> [Int]
(*$) l x = map (*x) l

-- 5) Definir las siguientes funciones usando listas por comprensión:

-- a) 'divisors', que dado un entero positivo 'x' devuelve la
-- lista de los divisores de 'x' (o la lista vacía si el entero no es positivo)
divisors :: Int -> [Int]
divisors x = [y | y <- [0.. x], mod x y == 0]

-- b) 'matches', que dados un entero 'x' y una lista de enteros descarta
-- de la lista los elementos distintos a 'x'
matches :: Int -> [Int] -> [Int]
matches n xs = [x | x <- xs, n == x]

-- c) 'cuadrupla', que dado un entero 'n', devuelve todas las cuadruplas
-- '(a,b,c,d)' que satisfacen a^2 + b^2 = c^2 + d^2,
-- donde 0 <= a, b, c, d <= 'n'
cuadruplas :: Int -> [(Int,Int,Int,Int)]
cuadruplas n = [(x,y,z,w) | x <- [0..n], y <- [0..n], z <- [0..n], w <- [0..n]
                            ,x^2 + y^2 == z^2 + w^2]

-- (d) 'unique', que dada una lista 'xs' de enteros, devuelve la lista
-- 'xs' sin elementos repetidos
unique :: [Int] -> [Int]
unique [] = []
unique xs = [x | (x, i) <- zip xs [0..], x `notElem` take i xs]

{- 
6) El producto escalar de dos listas de enteros de igual longitud
es la suma de los productos de los elementos sucesivos (misma
posición) de ambas listas.  Definir una función 'scalarProduct' que
devuelva el producto escalar de dos listas.

Sugerencia: Usar las funciones 'zip' y 'sum'. -}
scalarproduct :: [Int] -> [Int] -> Int
scalarproduct xs ys = sum $ zipWith (*) xs ys


-- 7) Definir mediante recursión explícita
-- las siguientes funciones y escribir su tipo más general:

-- a) 'suma', que suma todos los elementos de una lista de números
suma:: Num a => [a] -> a
suma [] = 0
suma [x] = x
suma (x:xs) = x + suma xs

-- b) 'alguno', que devuelve True si algún elemento de una
-- lista de valores booleanos es True, y False en caso
-- contrario
alguno :: [Bool] -> Bool
alguno [] = False
alguno [x] = x
alguno (x:xs) = if x then x else alguno xs

-- c) 'todos', que devuelve True si todos los elementos de
-- una lista de valores booleanos son True, y False en caso
-- contrario
todos :: [Bool] -> Bool
todos [] = False
todos [x] = x
todos (x:xs) = x && todos xs

-- d) 'codes', que dada una lista de caracteres, devuelve la
-- lista de sus ordinales
codes :: [Char] -> [Int]
codes [] = []
codes (x:xs) = (ord x - 97) : codes xs

-- e) 'restos', que calcula la lista de los restos de la
-- división de los elementos de una lista de números dada por otro
-- número dado
restos :: [Int] -> Int -> [Int]
restos xs x = if x /= 0 then map (mod x) xs else []

-- f) 'cuadrados', que dada una lista de números, devuelva la
-- lista de sus cuadrados
cuadrados :: [Int] -> [Int]
cuadrados xs = [x*x | x <- xs]

-- g) 'longitudes', que dada una lista de listas, devuelve la
-- lista de sus longitudes
longitudes :: [[a]] -> [Int]
longitudes [] = [0]
longitudes [x] = [length x]
longitudes (x:xs) = length x : longitudes xs

-- h) 'orden', que dada una lista de pares de números, devuelve
-- la lista de aquellos pares en los que la primera componente es
-- menor que el triple de la segunda
orden :: (Ord a, Num a) => [(a, a)] -> [(a, a)]
orden [] = []
orden (head : xs)   | x < 3*y = head : orden xs
                    | otherwise = orden xs
        where x = fst head
              y = snd head

-- i) 'pares', que dada una lista de enteros, devuelve la lista
-- de los elementos pares
pares :: Integral a => [a] -> [a]
pares [] = []
pares (x:xs) | even x = x : pares xs
             | otherwise = pares xs


-- j) 'letras', que dada una lista de caracteres, devuelve la
-- lista de aquellos que son letras (minúsculas o mayúsculas)
letras :: [Char] -> [Char]
letras [] = []
letras (x:xs) | not (isDigit x) = x : letras xs
              | otherwise = letras xs

-- k) 'masDe', que dada una lista de listas 'xss' y un
-- número 'n', devuelve la lista de aquellas listas de 'xss'
-- con longitud mayor que 'n'
masDe :: [[a]] -> Int -> [[a]]
masDe [] _ = [[]]
masDe (xs:xss) n | length xs > n = xs : masDe xss n
                 | otherwise = masDe xss n

