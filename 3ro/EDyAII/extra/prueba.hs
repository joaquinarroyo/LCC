module Prueba where
import ListSeq
import Par

-- data Tree a = E | L a | N (Tree a) a (Tree a) deriving Show

-- toList :: Tree a -> [a]
-- toList E = []
-- toList (L a) = [a]
-- toList (N l a r) = toList l ++ [a] ++ toList r

-- concatT :: Tree (Tree a) -> Tree a
-- concatT E = E
-- concatT (L t) = t
-- concatT (N t1 (L t) t2) = N (concatT t1) t (concatT t2)
-- concatT (N t1 (N t11 x t22) t2) =
--                             let 
--                                 t1' = concatT t1
--                                 t2' = concatT t2
--                             in N t1' x (N t11 x t2')


uniquify :: Eq a => [a] -> [a]
uniquify [] = []
uniquify (x:xs) = x : uniquify (filter (/= x) xs)

aa :: [Char] -> Int
aa s = reduceL (+) 0 (tabulateL (\i -> if nthL s i == 'a' && nthL s (i+1) == 'a'
                                        then 1 else 0) ((lengthL s) - 1))


ventas :: [Float] -> ([Float], Float)
ventas [] = ([], -1)
ventas (x:xs) = let
                    (l, last) = scanL (+) 0 (x:xs)
                    list = appendL (drop 1 l) (singletonL last)
                    res = reduceL appendL emptyL (tabulateL (\i -> if nthL xs i > (nthL list i)/(fromIntegral (i+1))
                                            then singletonL (nthL xs i)
                                            else emptyL) (lengthL xs))
                in
                    (appendL (singletonL x) res, x)

-- data Cadena = E | L Char | N Cadena Cadena deriving Show

-- f :: Int -> Char
-- f x = y
--     where
--         (y:ys) = show x

-- cToList :: Cadena -> [Char]
-- cToList E = []
-- cToList (L x) = [x]
-- cToList (N l r) = cToList l ++ cToList r

-- crearAux :: Int -> Int -> Int -> (Int -> Char) -> Cadena
-- crearAux n carry last f = if n == 1 then
--                             if carry == last || carry == 0
--                             then L '*'
--                             else L (f carry)
--                     else N (crearAux d carry last f) (crearAux (d+rest) (carry+d) last f)
--         where
--             d = div n 2
--             rest = mod n 2

-- crear :: Int -> (Int -> Char) -> Cadena
-- crear n f = N (crearAux d 0 (n+1) f) (crearAux (d+rest) d (n+1) f)
--         where
--             d = div (n+2) 2
--             rest = mod (n+2) 2

-- t = N (N (L 'a') (N (L 'b') (L 'c'))) (N (L 'b') (L 'a'))

-- palindromo :: Cadena -> Bool
-- palindromo E = True
-- palindromo (L x) = True
-- palindromo node@(N l r) = let
--                             l' = palindromo l
--                             r' = palindromo r
--                           in


dic = [(1, ["the","big","dog"]), (2, ["a", "big", "dog"]), (3, ["i", "read", "a", "book"])]
dic2 = makeIndex dic

makeIndex :: [(Integer, [String])] -> [(String, [(Integer, Int)])]
makeIndex xs = let 
                    xs' = joinL (tabulateL (\i -> tabulateL (\j -> 
                        (nthL (snd (nthL xs i)) j, ((fst (nthL xs i)), j))) (lengthL (snd (nthL xs i))))
                                                            (lengthL xs))
                in
                    collectL compare xs'
                            
moreUsed :: [(String, [(Integer, Int)])] -> String
moreUsed xs = let 
                xs' = mapL length' xs
              in
                fst (reduceL max' ("", 0) xs')
    where
        length' (s, l) = (s, length l)
        max' (s1, n1) (s2, n2) | n1 >= n2 = (s1, n1)
                               | otherwise = (s2, n2)

cantCeros :: [Int] -> Int
cantCeros xs = lengthL (filterL (==0) xs)

-- posUnosAux :: [Int] -> Int -> ([(Int, Int)], (Int, Int))
-- posUnosAux xs c1 = let
--                     xs' = tabulateL (\i -> (i, nthL xs i)) (length xs)
--                     in
--                         scanL f' (0, 0) xs'
--     where
--         f' (x, y) (w, z) = (w+c1, z)

-- posUnos :: [Int] -> [Int]
-- posUnos xs = posUnosAux xs c
--     where
--         c = cantCeros xs

-- splitBST :: Tree Int -> Int -> (Tree Int, Tree Int)
-- splitBST E _ = (E, E) 
-- splitBST (L x) n | n >= x = ((L x), E)
--                  | otherwise = (E, (L x))
-- splitBST (N i l x r) n  | n > x = 
--                                 let
--                                     (l', r') = splitBST r n
--                                 in
--                                     (N i l x l', r')
--                         | otherwise = 
--                                 let
--                                     (l', r') = splitBST l n
--                                 in
--                                     (l', N i r' x r)


data T a = E | L a | N Int (T a) (T a) deriving Show

t = N 6 (N 3 (N 2 (L (-1)) (L 2)) (L (-3))) (N 3 (N 2 (L 4) (L (8))) (L 6))

partirAux :: (Num a, Ord a) => T a -> Int -> (T (Int, a), T (Int, a))
partirAux E _ = (E, E)
partirAux (L x) index  | x >= 0 = (L (index, x), E)
                       | otherwise = (E, L (index, x))
partirAux (N i l r) index = let
                            ((lp, ln), (rp, rn)) = partirAux l index ||| partirAux r (index+size l)
                        in
                            (merge lp rp, merge ln rn)
    where
        size E = 0
        size (L _) = 1
        size (N i _ _) = i
        merge E E = E
        merge E (L x) = L x
        merge (L x) E = L x
        merge leaf1@(L x1) leaf2@(L x2) = N 2 leaf1 leaf2
        merge node@(N i l r) E = node
        merge E node@(N i l r) = node
        merge leaf@(L x) node@(N i l r) = N (i+1) leaf node
        merge node@(N i l r) leaf@(L x) = N (i+1) node leaf
        merge node1@(N il ll rl) node2@(N ir lr rr) = N (il + ir) node1 node2

partir :: (Num a, Ord a) => T a -> (T (Int, a), T (Int, a))
partir t = partirAux t 0


filterTAux :: (a -> Bool) -> T a -> Int -> T (Int, a)
filterTAux _ E _ = E
filterTAux p (L x) index | p x = (L (index, x))
                         | otherwise = E
filterTAux p (N i l r) index = let
                                    (l', r') = filterTAux p l index ||| filterTAux p r (index + size l)
                                in
                                    merge l' r'
    where
        size E = 0
        size (L _) = 1
        size (N i _ _) = i
        merge E E = E
        merge E (L (i, x)) = L (i, x)
        merge (L (i, x)) E = L (i, x)
        merge leaf1@(L (i1, x1)) leaf2@(L (i2, x2)) = N 2 leaf1 leaf2
        merge leaf@(L (il, x)) node@(N i l r) = N (i+1) leaf node
        merge node@(N i l r) leaf@(L (il, x)) = N (i+1) node leaf
        merge node1@(N il ll rl) node2@(N ir lr rr) = N (il + ir) node1 node2

filterT :: (a -> Bool) -> T a -> T (Int, a)
filterT p t = filterTAux p t 0


splitTAux :: (a -> Bool) -> T a -> Int -> (T (Int, a), T (Int, a))
splitTAux _ E _ = (E, E)
splitTAux p (L x) index | p x = (L (index, x), E)
                        | otherwise = (E, L (index, x))
splitTAux p (N i l r) index = let
                            ((lp, ln), (rp, rn)) = splitTAux p l index ||| splitTAux p r (index+size l)
                            in
                                (merge lp rp, merge ln rn)
    where
        size E = 0
        size (L _) = 1
        size (N i _ _) = i
        merge E E = E
        merge E (L x) = L x
        merge (L x) E = L x
        merge leaf1@(L x1) leaf2@(L x2) = N 2 leaf1 leaf2
        merge node@(N i l r) E = node
        merge E node@(N i l r) = node
        merge leaf@(L x) node@(N i l r) = N (i+1) leaf node
        merge node@(N i l r) leaf@(L x) = N (i+1) node leaf
        merge node1@(N il ll rl) node2@(N ir lr rr) = N (il + ir) node1 node2

splitT :: (a -> Bool) -> T a -> (T (Int, a), T (Int, a))
splitT p t = splitTAux p t 0

entradas :: [Int] -> Float -> [Int]
entradas xs p = let
                (xs', last) = scanL (+) 0 xs
                xs'' = appendL (drop 1 xs') (singletonL last)
                in
                    tabulateL (\i -> div (nthL xs'' i) (i+1)) (lengthL xs'')

incluidosAux :: [(Int, Int)] -> Int -> Int
incluidosAux xs n = let
                        xs' = tabulateL (\i -> mapL (f (nthL xs (n-i-1))) (takeL xs (n-i-1))) (n-2)
                    in
                        reduceL (+) 0 (joinL xs')
    where
        f (x, y) (z, w) = if x >= z && x+y <= z+w then 1 else 0 

incluidos :: [(Int, Int)] -> Int
incluidos xs = incluidosAux xs (lengthL xs)


-- aumentos :: [(Char, Int)] -> (Char, Int)
-- aumentos xs = let
--                 xs' = joinL (tabulateL (\i -> mapL (f (nthL xs i)) (dropL xs (i+1))) (lengthL xs))
--               in
--                 reduceL max' ('a', 0) xs''
--     where
--         f (art1, p1) (art2, p2) | art1 == art2 = if p1 < p2 then (art1, 1) else (art1, 0)
--                                 | otherwise = (art1, 0)

mapReduce :: (a -> b) -> (b -> b -> b) -> b -> [a] -> b
mapReduce m r e [] = e
mapReduce m r e [x] = r e (m x)
mapReduce m r e (x:y:xs) = r z (mapReduce m r e xs)
    where
        z = r (m x) (m y)