import Seq
import Par

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
showtL l = NODE l r
  where (l, r) = takeL l d ||| dropL l (d+rest)
        (d, rest) = (n `div` 2) ||| (n `mod` 2)
        n = lengthL l

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

instance Seq [] where
  emptyS = emptyL
  singletonS = singletonL
  lengthS = lengthL
  nthS = nthL
  tabulateS = tabulateL
  mapS = mapL
  filterS = filterL
  appendS = appendL
  takeS = takeL
  dropS = dropL
  showtS = showtL
  showlS = showlL
  joinS = joinL
  reduceS = reduceL
  scanS = scanL
  fromList = fromListL