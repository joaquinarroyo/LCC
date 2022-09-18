{-
1) 
    a- Eq, Num a,b => (a -> b) -> a -> Bool
    b- Ord a => a -> a -> Bool
    c- Eq a => a -> a -> Boobl
    d- Show a => a -> String

2)
    a- Num a => a -> a. Suma 5 al numero recibido.
    b- Ord a => a -> a. Chequea si el numero recibido es mayor a cero.
    c- [Char] -> [Char]. Hace cons de 'a' a la lista recibida.
    d- Show a => a -> a. Le agrega un '\n' al string recibido.
    e- Eq a => [a] -> [a]. Filtra los numeros de la lista que son iguales a 7.
    f- [[Int]] -> [[Int]]. Hace cons a cada elemento de la lista con [1].

4)  
    a- Bien formada. Resultado -> False
    b- Mal formada. Error sintactico.
    c- Bien formada. Resultado -> False
    d- Mal formada. Error sintactico.
    e- Bien formada. Resultado -> 0
    f- Bien formada. Resultado -> True
    g- Bien formada. Resultado -> True

5)
    a- 
    b- greater x y = x > y
    c- f x y = x

6)  
    a- smallest = \x -> \y -> \z -> if x < y and x < z then x else 
                                                if y < z and y < x 
                                                then y else z
    b- second = \x -> x
    c- andThen = \x -> \y -> if x then y else False
    d- twice = \x -> \y -> x (x y)
    e- flip = \f -> \x -> \y -> f y x
    f- inc = \x -> x + 1

8)
    f::c -> d
    g::a -> b -> c

    h x y = f (g x y)
    el tipo de h es h:: a->b->d

    El tipo de la funcion ◦ es (◦)::(a->b)->c
10)
    a- [[]] ++ xs = xs ->
    b- [[]] ++ xs = [xs] ->
    c- [[]] ++ xs = [] : xs -> 
    d- [[]] ++ xs = [[], xs] -> 
    e- [[]] ++ [xs] = [[], xs] -> 
    f- [[]] ++ [xs] = [xs] ->
    g- [] ++ [xs] = [] : [xs] ->
    h- [] ++ xs = xs ->
    i- [xs] ++ [] = [xs] ->
    j- [xs] ++ [xs] = [xs, xs] ->

11)
    a- Num a => [a] -> Float
    b- Num a => [a] -> [Float]
-}

-- 7)
-- a)

iff :: Bool -> Bool -> Bool
iff x y = if x then not y else y

-- b)
alpha :: a -> a
alpha x = x

-- 9)

zip3N :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3N _ _ [] = []
zip3N _ [] _ = []
zip3N [] _ _ = []
zip3N (x:xs) (y:ys) (z:zs) = (x,y,z) : zip3N xs ys zs

-- zip3S :: [a] -> [b] -> [c] -> [(a,b,c)]
-- zip3S (x:xs) (y:ys) (z:zs) = 


-- 13)
type NumBin = [Bool]

-- a)

sumBin :: NumBin -> NumBin -> NumBin
sumBin [] [] = []
sumBin [] (y:ys) = y : sumBin [] ys
sumBin(x:xs) [] = x : sumBin xs []
sumBin (x:xs:xss) (y:ys:yss) =
    if x && y then
        False : sumBin (True:xss) (ys:yss)
        else
            (x || y) : sumBin (xs:xss) (ys:yss)
sumBin (x:xs) (y:ys) =
    if null xs && null ys && x && y then
        False : (True : sumBin [] [])
        else
            (x || y) : sumBin xs ys

-- b)

prodBin :: NumBin -> NumBin -> NumBin
prodBin xs ys = prodBinSum (prodBinParse (prodBinAux xs ys) (length ys) 0)

prodBinAux :: NumBin -> NumBin -> NumBin
prodBinAux [] [] = []
prodBinAux xs ys = [y && x | y <- ys, x <- xs]

prodBinParse :: NumBin -> Int -> Int -> [NumBin]
prodBinParse [] _ _ = []
prodBinParse xs a b = prodAddFalse (take a xs) b : prodBinParse (drop a xs) a (b+1)

prodAddFalse :: NumBin -> Int -> NumBin
prodAddFalse [] _ = []
prodAddFalse (x:xs) a =
    if a > 0 then
        False : prodAddFalse (x:xs) (a-1)
        else
            x : prodAddFalse xs (a-1)

prodBinSum :: [NumBin] -> NumBin
prodBinSum = foldr sumBin []

-- c)

divBin2 :: NumBin -> NumBin
divBin2 [] = []
divBin2 (x:xs) = xs

restBin2 :: NumBin -> NumBin
restBin2 [] = []
restBin2 (x:xs) = [x]


-- 13)
-- a)
divisors :: Int -> [Int]
divisors 0 = []
divisors n = [x | x <- [1..n], n `mod` x == 0]

-- b)
matches :: Int -> [Int] -> [Int]
matches n xs = [x | x <- xs, n == x]

-- c)
cuadruplas :: Int -> [(Int,Int,Int,Int)]
cuadruplas n = [(x,y,z,w) | x <- [0..n], y <- [0..n], z <- [0..n], w <- [0..n]
                            ,x^2 + y^2 == z^2 + w^2]

-- d)
unique :: [Int] -> [Int]
unique [] = []
unique xs = [x | x <- xs, length (matches x xs) == 1]

-- 14)
scalarproduct :: [Int] -> [Int] -> Int
scalarproduct xs ys = sum $ zipWith (*) xs ys

-- prueba :: Ord a => a -> a -> a -> a
-- prueba x y z | x < y && x < z =  x
--              | y < z && y < x =  y
--              | otherwise = z

