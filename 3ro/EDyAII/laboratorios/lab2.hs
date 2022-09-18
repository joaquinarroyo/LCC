module Lab2 where

{-
   Laboratorio 2
   EDyAII 2022
-}

import Data.List

-- 1) Dada la siguiente definición para representar árboles binarios:

data BTree a = E | Leaf a | Node (BTree a) (BTree a)
instance Show a => Show (BTree a) where
    show E = show "Empty"
    show (Leaf x) = show x
    show (Node l r) = show l ++ " " ++ show r

arbol = Node (Node (Leaf 1) (Leaf 2)) (Node (Leaf 3) (Leaf 4))
{-
                    Node
             Node            Node
        Leaf 1  Leaf 2  Leaf 3  Leaf 4
-}

-- Definir las siguientes funciones:

-- a) altura, devuelve la altura de un árbol binario.

altura :: BTree a -> Int
altura E = 0
altura (Leaf _) = 0
altura (Node l r) = 1 + max (altura l) (altura r)

-- b) perfecto, determina si un árbol binario es perfecto (un árbol binario es perfecto si 
-- cada nodo tiene 0 o 2 hijos y todas las hojas están a la misma distancia desde la raı́z).

perfecto :: BTree a -> Bool
perfecto E = True
perfecto (Leaf _) = True
perfecto (Node l r) = (altura l == altura r) && perfecto l && perfecto r

-- c) inorder, dado un árbol binario, construye una lista con el recorrido inorder del mismo.

inorder :: Show a => BTree a -> [a]
inorder E = []
inorder (Leaf x) = [x]
inorder (Node l r) = inorder l ++ inorder r

-- 2) Dada las siguientes representaciones de árboles generales y de árboles binarios 
-- (con información en los nodos):

{- Definir una función g2bt que dado un árbol nos devuelva un árbol binario de la siguiente manera:
   la función g2bt reemplaza cada nodo n del árbol general (NodeG) por un nodo n' del 
   árbol binario (NodeB ), donde el hijo izquierdo de n' representa el hijo 
   más izquierdo de n, y el hijo derecho de n' representa al hermano derecho
   de n, si existiese (observar que de esta forma, el hijo derecho de la raı́z es siempre vacı́o).
   
   
   Por ejemplo, sea t: 
       
                    A 
                 / | | \
                B  C D  E
               /|\     / \
              F G H   I   J
             /\       |
            K  L      M    
   
   g2bt t =
         
                  A
                 / 
                B 
               / \
              F   C 
             / \   \
            K   G   D
             \   \   \
              L   H   E
                     /
                    I
                   / \
                  M   J  
-}
data GTree a = EG | NodeG a [GTree a]
instance Show a => Show (GTree a) where
    show EG = show "EG"
    show (NodeG x xs) = "(" ++ show x ++ " " ++ show xs ++ ")"

data BinTree a = EB | NodeB (BinTree a) a (BinTree a)
instance Show a => Show (BinTree a) where
    show EB = show "EB"
    show (NodeB l x r) = "(" ++ show l ++ " " ++ show x ++ " " ++ show r ++ ")"

arbol2 = NodeG 'A' [NodeG 'B' [NodeG 'F' [], NodeG 'G' [], NodeG 'H' []],
                NodeG 'C' [], NodeG 'D' [], NodeG 'E' [NodeG 'I' [NodeG 'M' []], NodeG 'J' []]]

g2btRigth :: [GTree a] -> BinTree a
g2btRigth [] = EB
g2btRigth (EG:ys) = EB
g2btRigth [NodeG x _] = NodeB EB x EB
g2btRigth ((NodeG x _):ys) = NodeB EB x (g2btRigth ys)

g2btAux :: GTree a -> [GTree a] -> BinTree a
g2btAux EG [] = EB
g2btAux EG [NodeG x []] = NodeB EB x EB
g2btAux EG (y:ys) = g2btRigth (y:ys)
g2btAux (NodeG x []) (y:ys) = NodeB EB x (g2btAux y ys)
g2btAux (NodeG x []) [] = NodeB EB x EB
g2btAux (NodeG x (xs:xss)) [] = NodeB (g2btAux xs xss) x EB
g2btAux (NodeG x (xs:xss)) (y:ys) = NodeB (g2btAux xs xss) x (g2btAux y ys)

g2bt :: GTree a -> BinTree a
g2bt EG = EB
g2bt (NodeG x []) = NodeB EB x EB
g2bt (NodeG x (xs:xss)) = NodeB (g2btAux xs xss) x EB


-- 3) Utilizando el tipo de árboles binarios definido en el ejercicio anterior, 
-- definir las siguientes funciones: 
t = NodeB (NodeB EB 2 (NodeB EB 4 EB)) 1 (NodeB (NodeB EB 5 EB) 3 (NodeB EB 6 EB))

-- Funciones auxiliares ------------------------------------------------------------

-- Calcula la altura de un BinTree
alturaBinTree :: BinTree a -> Int
alturaBinTree EB = 0
alturaBinTree (NodeB EB _ EB) = 0
alturaBinTree (NodeB l _ r) = 1 + max (alturaBinTree l) (alturaBinTree r)

-- Devuelve los items de un BinTree desde el nivel mas profundo hasta la raiz
-- itemsPerLevel t = [[7, 4, 5, 6], [2, 3], [1]]
itemsPerLevel :: BinTree a -> Int -> [[a]]
itemsPerLevel EB _ = []
itemsPerLevel tree n | n >= 0 = itemsInLevel tree 0 n : itemsPerLevel tree (n-1)
                     | otherwise = []

-- Devuelve los items del nivel recibido en el BinTree recibido
-- itemsInLevel t 2 = [7, 4, 5, 6]
itemsInLevel :: BinTree a -> Int -> Int -> [a]
itemsInLevel EB _ _ = []
itemsInLevel (NodeB l x r) nivelActual nivel =
   if 2^nivelActual == 2^nivel then
      [x]
   else
       itemsInLevel l (nivelActual+1) nivel ++ itemsInLevel r (nivelActual+1) nivel

-------------------------------------------------------------------------------------
-- a) dcn, que dado un árbol devuelva la lista de los elementos que se encuentran 
-- en el nivel más profundo que contenga la máxima cantidad de elementos posibles.

dcn :: BinTree a -> [a]
dcn EB = []
dcn tree = dcnAux list (length list - 1)
   where
      list = itemsPerLevel tree (alturaBinTree tree)

-- Chequeo si 2^level es igual a la cantidad de elementos en el nivel 'level'
-- si esto pasa devuelvo la lista ya que el nivel esta completo, y estamos viendo
-- recorriendo desde lo items del nivel mas bajo hacia la raiz
dcnAux :: [[a]] -> Int -> [a]
dcnAux [] _ = []
dcnAux (x:xs) c | 2^c == length x = x
                | otherwise = dcnAux xs (c-1)

{- b) maxn, que dado un árbol devuelva la profundidad del nivel completo
      más profundo. Por ejemplo, maxn t = 2  -}

maxn :: BinTree a -> Int
maxn EB = 0
maxn tree = maxnAux list (length  list - 1)
   where
      list = itemsPerLevel tree (alturaBinTree tree)

-- Similar que dcnAux pero en lugar de devolver la lista devuelvo el level
maxnAux :: [[a]] -> Int -> Int
maxnAux [] _ = 0
maxnAux (x:xs) c | 2^c == length x = c
                 | otherwise = maxnAux xs (c-1)

{- c) podar, que elimine todas las ramas necesarias para transformar
      el árbol en un árbol completo con la máxima altura posible. 
      Por ejemplo,
         podar t = NodeB (NodeB EB 2 EB) 1 (NodeB EB 3 EB)
-}

podar :: BinTree a -> BinTree a
podar EB = EB
podar tree = podarAux tree (maxn tree)

-- Recorro el arbol hasta (maxn tree) el cual me indica el nivel mas profundo completo
-- por lo cual es el ultimo que vamos a incluir antes de eliminar lo que nos quede del arbol.
podarAux :: BinTree a -> Int -> BinTree a
podarAux EB _ = EB
podarAux (NodeB l x r) c | c >= 0 = NodeB (podarAux l (c-1)) x (podarAux r (c-1))
                         | otherwise = EB

