{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Practica4 where

-- 1

data Tree a = Leaf a | Node (Tree a) (Tree a) deriving Show

completo :: a -> Int -> Tree a
completo x 0 = Leaf x
completo x n = let node = completo x (n-1) in Node node node

divisionPorDos :: Int -> (Int, Int)
divisionPorDos = divisionPorDosAux 0

divisionPorDosAux :: Int -> Int -> (Int, Int)
divisionPorDosAux i j | j == 0 || j == 1 = (i, j)
                      | otherwise = divisionPorDosAux (i+1) (j-2)

balanceado :: a -> Int -> Tree a
balanceado x 1 = Leaf x
balanceado x n | x2 == 0 = Node node node
               | otherwise = Node (balanceado x x1) (balanceado x (x1+x2))
    where
        (x1, x2) = divisionPorDos n
        node = balanceado x x1

-- 2

data BSTRee a = BSTLeaf | BSTNode (BSTRee a) a (BSTRee a) deriving Show

maximumBST :: BSTRee a -> a
maximumBST (BSTNode BSTLeaf x BSTLeaf) = x
maximumBST (BSTNode l x BSTLeaf) = x
maximumBST (BSTNode BSTLeaf x r) = maximumBST r
maximumBST (BSTNode l _ r) = maximumBST r

minimumBST :: BSTRee a -> a
minimumBST (BSTNode BSTLeaf x BSTLeaf) = x
minimumBST (BSTNode BSTLeaf x r) = x
minimumBST (BSTNode l x BSTLeaf) = minimumBST l
minimumBST (BSTNode l _ r) = minimumBST l

checkBST :: Ord a => BSTRee a -> Bool
checkBST BSTLeaf = True
checkBST (BSTNode l x r) = checkBST l && checkBST r && (maximumBST l < x) && (x < minimumBST r)

t = BSTNode (BSTNode BSTLeaf 1 BSTLeaf) 5 (BSTNode BSTLeaf 7 BSTLeaf)
t1 = BSTNode (BSTNode BSTLeaf 2 BSTLeaf) 4 (BSTNode BSTLeaf 6 BSTLeaf)

splitBST :: Ord a => BSTRee a -> a -> (BSTRee a, BSTRee a)
splitBST BSTLeaf _ = (BSTLeaf, BSTLeaf)
splitBST (BSTNode l x r) n | x <= n = let (l', r') = splitBST r n in (BSTNode l x l', r')
                           | x > n = let (l', r') = splitBST l n in (l', BSTNode r' x r)

-- 3

member :: Ord a => a -> BSTRee a -> Bool
member _ BSTLeaf = False
member x (BSTNode l y r) | x == y = True
                         | x < y = member x l
                         | x > y = member x r



-- Ejercicio de parcial 2019 ---------------------------------------------------------------

data Treap p k = E | N (Treap p k) p k (Treap p k) deriving Show

treap = N (N (N E 2 'a' E) 4 'c' (N E 0 'e' E)) 9 'h' E

-- Funciones auxiliares --------------------------------------------------------------------
maximumKeyTreap :: Treap p k -> k
maximumKeyTreap (N l p k E) = k
maximumKeyTreap (N l p k r) = maximumKeyTreap r

minimumKeyTreap :: Treap p k -> k
minimumKeyTreap (N E p k r) = k
minimumKeyTreap (N l p k r) = minimumKeyTreap l

rotateL :: Treap p k -> Treap p k
rotateL (N l p k (N rl rp rk rr)) = N (N l p k rl) rp rk rr

rotateR :: Treap p k -> Treap p k
rotateR (N (N ll lp lk lr) p k r) = N ll lp lk (N lr p k r)

splitAux :: Treap p k -> (Treap p k, Treap p k)
splitAux (N l _ _ r) = (l, r)
--------------------------------------------------------------------------------------------
-- a)
key :: Treap p k -> k
key (N _ _ key _) = key

-- b)
priority :: Treap p k -> p
priority (N _ pr _ _) = pr

-- c)
isTreap :: (Ord k, Ord p) => Treap p k -> Bool
isTreap E = True
isTreap (N left@(N ll lp lk lr) p k right@(N rl rp rk rr)) =
    p >= lp && p >= rp && maximumKeyTreap left < k && minimumKeyTreap right > k &&
    isTreap left && isTreap right
isTreap (N left@(N ll lp lk lr) p k E) = p >= lp && maximumKeyTreap left < k && isTreap left
isTreap (N E p k right@(N rl rp rk rr)) = p >= rp && minimumKeyTreap right > k
isTreap (N E p k E) = True

-- (Hay que escribir la recurrencia segun el trabajo de esta funcion, i.e W_{isTreap}(n)

-- d)
insert :: (Ord k, Ord p) => k -> p -> Treap p k -> Treap p k
insert key priority E = N E priority key E
insert key priority node@(N l p k r) | key > k && priority > p = rotateL (N l p k (insert key priority r))
                                     | key < k && priority > p = rotateR (N (insert key priority l) p k r)
                                     | key > k = N l p k (insert key priority r)
                                     | key < k = N (insert key priority l) p k r
                                     | otherwise = node

-- e)
split :: (Ord k, Ord p, Num p) => k -> Treap p k -> (Treap p k, Treap p k)
split key node@(N l p k r) = splitAux (insert key (p+1) node)

------------------------------------------------------------------------------------------
-- Ejercicio  7 de practica 4 ---------------------------------------------------------------

data PHeaps a = Empty | Root a [PHeaps a] deriving Show

heap = Root 1 [Root 2 [Root 3 [Empty]], Root 5 [Empty]]

-- Funciones auxiliares ------------------------------------------------------------------
minList :: Ord a => a -> [PHeaps a] -> a
minList value [] = value
minList value [Empty] = value
minList _ [Root value _] = value
minList value (Empty:xs) = minList value xs
minList value ((Root val _):xs) = min val (minList value xs)

checkFalse :: [Bool] -> Bool
checkFalse [True] = True
checkFalse [False] = False
checkFalse (x:xs) = x && checkFalse xs

-------------------------------------------------------------------------------------------
-- a)
isHeap :: Ord a => PHeaps a -> Bool
isHeap Empty = True
isHeap (Root value childs) = 
    value <= minList value childs && checkFalse (map (isHeap) childs)

-- b)
merge :: Ord a => PHeaps a -> PHeaps a -> PHeaps a
merge Empty Empty = Empty
merge Empty heap = heap
merge heap Empty = heap
merge root1@(Root val1 childs1) root2@(Root val2 childs2) | val1 > val2 = Root val2 ([root1]++childs2)
                                                          | val1 <= val2 = Root val1 ([root2]++childs1)

-- c)
insertHeap :: Ord a => a -> PHeaps a -> PHeaps a
insertHeap val Empty = Root val []
insertHeap val root@(Root val1 childs) = merge (Root val []) root

-- d)
concatHeaps :: Ord a => [PHeaps a] -> PHeaps a
concatHeaps [] = Empty
concatHeaps [x] = x
concatHeaps (x:xs) = merge x (concatHeaps xs)

-- e) La idea es quitar el elemento de la raiz (que va a ser el minimo), buscar el elemento
-- minimo en sus hijos, poner a ese como nueva raiz, y como sus hijos, sus previos hermanos 
-- sin el. Lo demas queda igual

delMin :: Ord a => PHeaps a -> Maybe (a, PHeaps a)
delMin Empty = Nothing
delMin (Root val childs) = Just (val, concatHeaps childs)

---------------------------------------------------
data Cadena = Nada | L Char | Nodo Cadena Cadena deriving Show


crear :: String -> Cadena
crear [] = Nada
crear [x] = L x
crear s = Nodo (crear (take n s)) (crear (drop n s))
    where
        n = div (length s) 2

cadena = crear "hola"

cadenaInOrder :: Cadena -> String
cadenaInOrder Nada = []
cadenaInOrder (L x) = [x]
cadenaInOrder (Nodo l r) = cadenaInOrder l ++ cadenaInOrder r

cadenaPostOrder :: Cadena -> String
cadenaPostOrder Nada = []
cadenaPostOrder (L x) = [x]
cadenaPostOrder (Nodo l r) = cadenaPostOrder r ++ cadenaPostOrder l

palindromo :: Cadena -> Bool
palindromo cadena = cadenaInOrder cadena == cadenaPostOrder cadena


--------------------------------------------------------
type Name = String
type Path = [Name]
data DirTree a = Dir Name [DirTree a] | File Name a deriving Show

mkDir :: Path -> Name -> DirTree a -> DirTree a
mkDir p n d = mkdir ("/":p) n d

mkdir :: Path -> Name -> DirTree a -> DirTree a
mkdir [x] name dir@(Dir dirName files) | x == dirName && (check name files) = 
                                                (Dir dirName (files++[Dir name []]))
                                       | otherwise = dir
mkdir (x:xs) name dir@(Dir dirName files) | x == dirName = 
                                                (Dir dirName (map (mkdir xs name) files))
                                          | otherwise = dir

check :: Name -> [DirTree a] -> Bool
check name [] = True
check name ((File fName _):xs) = name == fName && (check name xs)
check name ((Dir dirName _):xs) = name == dirName && (check name xs)

-- ls :: Path -> DirTree a -> [Name]
-- ls p t = lsAux ("/":p) t

lsAux :: Path -> DirTree a -> [Name]
lsAux [x] dir@(Dir dirName files) | x == dirName = showFiles files
                                  | otherwise = []
lsAux (x:xs:[]) dir@(Dir dirName files) | x == dirName = lsAux [xs] (search xs files)
                                        | otherwise = []
lsAux (x:xs:xss) dir@(Dir dirName files) | x == dirName = lsAux (xs:xss) (search xs files)
                                         | otherwise = []

showFiles :: [DirTree a] -> [Name]
showFiles [] = []
showFiles ((File fName _):xs) = fName : (showFiles xs)
showFiles ((Dir dirName _):xs) = dirName : (showFiles xs)

search :: Name -> [DirTree a] -> DirTree a
search name ((File fName _):xs) = search name xs
search name (dir@(Dir dirName _):xs) | name == dirName = dir
                                     | otherwise = search name xs

dir = Dir "/" [Dir "Home" [Dir "Pancho" [Dir "XD" [File "name" "xxs"]]], Dir "Pepe" []]