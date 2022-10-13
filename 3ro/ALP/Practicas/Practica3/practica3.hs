data BinTree a = Leaf | Bin a (BinTree a) (BinTree a) deriving Show

foldBin :: BinTree a -> b -> (a -> b -> b -> b) -> b
foldBin Leaf l b = l
foldBin (Bin a t u) l b = b a (foldBin t l b) (foldBin u l b)

isLeaf :: BinTree a -> Bool
isLeaf t = foldBin t True (\x y z -> False) 

mapBin :: (a -> b) -> BinTree a -> BinTree b
mapBin f t = foldBin t Leaf (\ x y z -> (Bin (f x) y z))

heigthBin :: BinTree a -> Int
heigthBin t = foldBin t 0 (\ x y z -> 1 + max y z)

mirrorBin :: BinTree a -> BinTree a
mirrorBin t = foldBin t Leaf (\x y z -> Bin x z y)

t = Bin 2 (Bin 4 Leaf Leaf) (Bin 3 (Bin 4 Leaf Leaf) Leaf)