import Par

-- aux
toList :: BTree a -> [a]
toList Empty = []
toList (Node _ l x r) = toList l ++ [x] ++ toList r

size :: BTree a -> Int
size Empty = 0
size (Node i _ _ _) = i

-- 1) --------------------------------------------------------------------------------------

data BTree a = Empty | Node Int (BTree a) a (BTree a) deriving Show
btree = Node 5 (Node 3 (Node 1 Empty 2 Empty) 3 (Node 1 Empty 4 Empty)) 5 (Node 1 Empty 6 Empty)

-- a)
nth :: BTree a -> Int -> a
nth (Node _ l x r) n | size l == n   = x
                     | size l >= n+1 = nth l n
                     | otherwise     = nth r (n - (size l) - 1)

-- b)
cons :: a -> BTree a -> BTree a
cons x1 Empty = Node 1 Empty x1 Empty
cons x1 (Node i l x r) = Node i (cons x1 l) x r

-- c)
tabulate :: (Int -> a) -> Int -> BTree a
tabulate f 0 = Empty
tabulate f n = let ((l, m), r) = (tabulate f d1) ||| (f d1) ||| (tabulate f' d2)
                    in Node n l m r
    where
        f' = \x -> f (x+d1+1)
        d1 = div n 2
        d2 = div (n-1) 2

-- d)
map' :: (a -> b) -> BTree a -> BTree b
map' _ Empty = Empty
map' f (Node i l x r) = let ((l', m), r') = (map' f l) ||| (f x) ||| (map' f r)
                        in Node i l' m r'

-- e)
take' :: Int -> BTree a -> BTree a
take' _ Empty = Empty
take' 0 _ = Empty
take' n (Node i l x r) | size l == n-1 = Node i l x Empty
                       | size l < n-1 = Node i l x (take' (n - (size l) - 1) r)
                       | otherwise = take' n l

-- f)
drop' :: Int -> BTree a -> BTree a
drop' _ Empty = Empty 
drop' 0 t = t
drop' n (Node i l x r) | size l == n-1 = r
                       | size l < n-1 = drop' (n - (size l) - 1) r
                       | otherwise = Node i (drop' n l) x r

-- 2) --------------------------------------------------------------------------------------
data Tree a = Em | Leaf a | Join (Tree a) (Tree a) deriving (Show, Eq)

mapT :: (a -> b) -> Tree a -> Tree b
mapT f Em          = Em
mapT f (Leaf x)   = Leaf (f x)
mapT f (Join l r) = let (l', r') = mapT f l ||| mapT f r
                    in Join l' r'

reduceT :: (a -> a -> a) -> a -> (Tree a) -> a
reduceT _ e Em          = e
reduceT _ _ (Leaf x)   = x
reduceT f e (Join l r) = let (l', r') = reduceT f e l ||| reduceT f e r
                         in f l' r'

mapreduce :: (a -> b) -> (b -> b -> b) -> b -> Tree a -> b
mapreduce _ _ e Em = e
mapreduce f _ _ (Leaf x) = f x
mapreduce f g e (Join l r) =  let (l', r') = (mapreduce f g e l) ||| (mapreduce f g e r)
                               in g l' r'

-- a)
-- base :: 

-- mcss :: (Num a, Ord a) => Tree a -> a
-- mcss t = mapreduce 

-- 3) --------------------------------------------------------------------------------------
max1 = Join (Leaf 2) (Leaf 5)
max2 = Join (Leaf 2) (Join (Leaf 3) (Leaf 6))
max3 = Join (Leaf max1) (Leaf max2)

-- sufijos :: Tree Int -> Tree (Tree Int)

-- conSufijos :: Tree Int -> Tree (Int, Tree Int)

maxT :: Tree Integer -> Integer
maxT t = reduceT max 0 t

maxAll :: Tree (Tree Integer) -> Integer
maxAll t = mapreduce maxT max 0 t

-- 4) --------------------------------------------------------------------------------------
data T a = E | N (T a) a (T a) deriving Show
t1 = N (N E 1 E) 2 E
t2 = N (N E 1 E) 2 (N (N E 3 E) 4 (N E 5 E)) 

altura :: T a -> Int
altura E = 0
altura (N l x r) = 1 + max (altura l) (altura r)

toListT :: T a -> [a]
toListT E = []
toListT (N l x r) = toListT l ++ [x] ++ toListT r

-- a)
combinar :: T a -> T a -> T a
combinar E E = E
combinar E node@(N _ _ _) = node
combinar node@(N _ _ _) E = node
combinar (N l1 x1 r1) (N l2 x2 r2) = 
    let (r1', r2') = (combinar l1 r1) ||| (combinar (combinar l2 r2) (N E x2 E))
                                    in N r1' x1 r2'

-- b)
filterT :: (a -> Bool) -> T a -> T a
filterT _ E = E
filterT f (N l x r) | f x = let (l', r') = (filterT f l) ||| (filterT f r)
                                in N l' x r'
                    | otherwise = let (l', r') = (filterT f l) ||| (filterT f r)
                                in combinar l' r'

-- c)
quicksortT :: T Integer -> T Integer
quicksortT E = E                                        
quicksortT (N l x r) = let (l', r') = filterT (<=x) l ||| (filterT (<=x) r)
                           (l'', r'') =filterT (>x) l  ||| (filterT (>x) r)
                           (l''', r''') = quicksortT (combinar l' r') ||| quicksortT (combinar l'' r'')
                            in N (quicksortT l''') x (quicksortT r''')

-- 5) --------------------------------------------------------------------------------------
unbalanced = Node 5 (Node 1 Empty 1 Empty) 2 (Node 3 (Node 2 (Node 1 Empty 1 Empty) 3 Empty) 4 Empty)
unbalanced2 = Node 4 Empty 1 (Node 3 Empty 2 (Node 2 Empty 1 (Node 1 Empty 1 Empty)))

altura' :: BTree a -> Int
altura' Empty = 0 
altura' (Node _ l _ r) = 1 + altura' l + altura' r

-- a)
splitAtT :: BTree a -> Int -> (BTree a, BTree a)
splitAtT t n = take' n t ||| drop' n t

-- b)
checkBalance :: BTree a -> BTree a -> Bool
checkBalance t1 t2 = altura' t1 == altura' t2 || altura' t1 == (altura' t2) - 1 
                  || (altura' t1) - 1 == altura' t2 

rebalance :: BTree a -> BTree a
rebalance Empty = Empty                                             
rebalance node@(Node _ Empty x Empty) = node                        -- chequear i
rebalance node@(Node i (Node li ll lx lr) x Empty) = rebalance (Node i ll lx (Node (size lr + 1) lr x Empty))
rebalance node@(Node i Empty x (Node ri rl rx rr)) = rebalance (Node i (Node (size rl + 1) Empty x rl) rx rr)
rebalance node@(Node i l@(Node li ll lx lr) x r@(Node ri rl rx rr)) 
                                        | checkBalance l r = node
                                        | altura' l > altura' r = 
                                            rebalance (Node i ll lx (Node ri lr x r))
                                        | otherwise =
                                            rebalance (Node i (Node li l x rl) rx rr)