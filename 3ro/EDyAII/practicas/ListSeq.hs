module ListSeq where
import Par

data TreeView a t = EMPTY | ELT a | NODE t t deriving Show
data ListView a t = NIL | CONS a t deriving Show

emptyL :: [a]
emptyL = []

singletonL :: a -> [a]
singletonL x = [x]

lengthL :: [a] -> Int
lengthL [] = 0
lengthL (x:xs) = 1 + lengthL xs

nthL :: [a] -> Int -> a
nthL (x:xs) 0 = x
nthL (x:xs) n = nthL xs (n-1)

tabulateL :: (Int -> a) -> Int -> [a]
tabulateL f n = [f i | i <- [0..n-1]]

mapL :: (a -> b) -> [a] -> [b]
mapL f [] = []
mapL f (x:xs) = f x : mapL f xs

filterL :: (a -> Bool) -> [a] -> [a]
filterL p [] = []
filterL p (x:xs) | p x       = x : filterL p xs
                 | otherwise = filterL p xs

appendL :: [a] -> [a] -> [a]
appendL [] ys = ys
appendL xs [] = xs
appendL (x:xs) ys = x : appendL xs ys

takeL :: [a] -> Int -> [a]
takeL [] _ = []
takeL (x:xs) 0 = []
takeL (x:xs) n = x : takeL xs (n-1)

dropL :: [a] -> Int -> [a]
dropL [] _ = []
dropL (x:xs) 0 = (x:xs)
dropL (x:xs) n = dropL xs (n-1)

showtL :: [a] -> TreeView a [a]
showtL [] = EMPTY
showtL [x] = ELT x
showtL xs = let
            n = length xs `div` 2
            (l, r) = takeL xs n ||| dropL xs n
            in NODE l r

showlL :: [a] -> ListView a [a]
showlL [] = NIL
showlL [x] = CONS x []
showlL l = CONS (head l) (tail l)

joinL :: [[a]] -> [a]
joinL [] = []
joinL (x:xs) = x ++ joinL xs

reduceL :: (a -> a -> a) -> a -> [a] -> a
reduceL f x [] = x
reduceL f x [y] = f x y
reduceL f x ys = let xs = contractL f ys
                  in reduceL f x xs
                  
-- aux ----------------------------------------------------
contractL :: (a -> a -> a) -> [a] -> [a]
contractL f [] = []
contractL f [x] = [x]
contractL f (x:y:xs) =
          let 
            (x', x'') = (f x y) ||| (contractL f xs)
          in 
            x' : x''

expandL :: (a -> a -> a) -> [a] -> [a] -> [a] 
expandL f xs ys =
          let
            l = lengthL xs
          in
            tabulateL (\i -> if even i
                            then nthL ys (i `div` 2)
                            else f (nthL ys (i `div` 2)) (nthL xs (i-1))) l
---------------------------------------------------------

scanL :: (a -> a -> a) -> a -> [a] -> ([a], a)
scanL f x [] = ([], x)
scanL f x [y] = ([x], f x y)
scanL f x l = 
            let 
            xs = contractL f l
            (l', t) = scanL f x xs
            in (expandL f l l', t)
    
fromListL :: [a] -> [a]
fromListL l = l

------ 7 pract 7 ---------------------------------------------------

mergeL :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeL f [] ys = ys
mergeL f xs [] = xs
mergeL f (x:xs) (y:ys) =
          case f x y of
            LT -> x : mergeL f xs (y:ys)
            EQ -> x : y : mergeL f xs ys
            GT -> y : mergeL f (x:xs) ys

sortL :: (a -> a -> Ordering) -> [a] -> [a]
sortL f xs = case showtL xs of
              EMPTY -> []
              (ELT e) -> xs
              (NODE l r) -> let
                              xs1 = sortL f l
                              xs2 = sortL f r
                            in
                              mergeL f xs1 xs2

maxEL :: (a -> a -> Ordering) -> [a] -> a
maxEL f xs = reduceL (\x y -> if f x y == GT then x else y) (nthL xs 0) xs

maxSL :: (a -> a -> Ordering) -> [a] -> Int
maxSL f xs = snd (reduceL (\(x, xi) (y, yi) -> if f x y == LT then (x, xi) else (y, yi)) 
                  (nthL xs 0, 0) ((tabulateL (\i -> (nthL xs i, i))) (lengthL xs))
                  )

groupL :: (a -> a -> Ordering) -> [a] -> [a]
groupL f xs = appendL 
                (mapL (\(x, y) -> x) ((filterL (\(x, v) -> v == 1) 
                (tabulateL (\i -> if (f (nthL xs i) (nthL xs (i+1))) == EQ 
                                then (nthL xs i, 0) 
                                else (nthL xs i, 1)) (lengthL xs - 1))
                                )))
                (singletonL (nthL xs (lengthL xs - 1)))

collectL :: Ord a => (a -> a -> Ordering) -> [(a, b)] -> [(a, [b])]
collectL f xs = let 
                  xs' = groupL f (sortL f (mapL fst xs))
                in 
                  mapL (\x -> (x, mapL snd (filterL (\(a, b) -> f a x == EQ ) xs))) xs'


  





