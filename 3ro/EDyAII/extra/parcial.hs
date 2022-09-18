
data Tree a = E | L a |N a (Tree a) (Tree a) deriving Show

t = N 1 (N 4 E E) (N 3 E E)
t1 = cons 0 t
t2 = cons 2 t

-- aux
inorder :: Tree a -> [a]
inorder E = []
inorder (L x) = [x]
inorder (N x l r) = inorder l ++ [x] ++ inorder r

size :: Tree a -> Int
size E = 0
size (L _) = 1
size (N _ l r) = 1 + size l + size r

-- a
cons :: Ord a => a -> Tree a -> Tree a
cons x tree | not (elemT x tree) = cons' x tree
            | otherwise = tree

cons' :: Ord a => a -> Tree a -> Tree a
cons' x E = L x
cons' x1 leaf@(L x2) | x1 > x2 = N x2 (L x1) E
                     | x1 < x2 = N x1 E (L x2)
                     | otherwise = leaf
cons' x1 node@(N x2 l r) | x1 > x2 = N x2 (cons' x1 l) r
                         | x1 < x2 = N x1 E node
                         | otherwise = node

-- b
subsequence :: Ord a => Tree a -> Int -> Int -> Tree a
subsequence E _ _ = E
subsequence leaf@(L x) i j | i == 0 = leaf
                           | otherwise = E
subsequence node@(N x l r) i j | index >= i && index <= j = N x 
                                                (subsequenceAux l i j 0) 
                                                (subsequenceAux r i j (index +1))
                               | index > j = subsequenceAux l i j 0
                               | index < i = subsequenceAux r i j (index+1)
                               | otherwise = E
    where
        index = size l

subsequenceAux :: Ord a => Tree a -> Int -> Int -> Int -> Tree a
subsequenceAux E _ _ _= E
subsequenceAux leaf@(L x) i j index | index >= i && index <= j = leaf
                                    | otherwise = E
subsequenceAux node@(N x l r) i j index | index' >= i && index' <= j = N x 
                                                        (subsequenceAux l i j index) 
                                                        (subsequenceAux r i j (index'+1))
                                        | index' > j = subsequenceAux l i j index
                                        | index' < j = subsequenceAux r i j (index'+1)
                                        | otherwise = E
    where
        index' = index + size l

-- c
elemT :: Eq a => a -> Tree a -> Bool
elemT x E = False
elemT x (L x1) = x == x1
elemT x (N x1 l r) | x == x1 = True
                   | otherwise = elemT x l || elemT x r


-- d
neighboursL :: Ord a => a -> Tree a -> Maybe a
neighboursL _ E = Nothing
neighboursL _ (L _) = Nothing
neighboursL x (N x1 l r) | elemT x l = neighboursL' x l Nothing
                         | elemT x r = neighboursL' x l (Just x1)
                         | otherwise = Nothing -- aca le erre, segui buscando en lugar de retornar

neighboursL' :: Ord a => a -> Tree a -> Maybe a -> Maybe a
neighboursL' _ E value = value
neighboursL' _ (L _) value = value
neighboursL' x (N x1 l r) value | elemT x l = neighboursL' x l value
                                | elemT x r = neighboursL' x l (Just x1)
                                | otherwise = value