{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module TP1 where

-- TP1 - Estructuras de Datos y Algoritmos II - Emiliano Montoro, Arroyo Joaquin
-- estructura de datos TTree
data TTree k v = Node k (Maybe v) (TTree k v) (TTree k v) (TTree k v)
               | Leaf k v
               | E
               deriving (Show, Eq)

-- Arboles de pruebas
t = Node 'r' Nothing E (Node 'e' (Just 16) (Node 'a' Nothing E (Leaf 's' 1) E)
    (Node 'o' (Just 2) (Leaf 'd' 9)
    E
    (Leaf 's' 4))
    E)
    (Node 's' Nothing E (Node 'i' (Just 4) (Leaf 'e' 8)
    (Leaf 'n' 7)
    E)
    E)

t1 = Node 'h' Nothing E (Node 'o' Nothing E (Node 'l' (Just 2) E (Leaf 'a' 4) E) E) E

t2 = Node 'h' Nothing E (Node 'o' (Just 2) (Node 'a' (Just 4) E E (Leaf 'k' 5)) E E ) E

-- 1) Funcion search 
-- Dada una clave y un arbol, devuelve el valor asociado a la clave, 
-- o Nothing si la clave no esta en el arbol.
search :: Ord k => [k] -> TTree k v -> Maybe v
search _ E = Nothing
search [] _ = Nothing
search [k] (Leaf key value) | k == key = Just value
search (k:ks) (Leaf _ _) = Nothing
search [k] (Node key value _ _ _) | k == key = value
search keys@(k:ks) (Node key value l m r) | k > key = search keys r
                                          | k < key = search keys l
                                          | otherwise = search ks m

-- 2) Funcion insert
-- Dada una clave y un valor, inserta la clave y el valor en el arbol.
-- Si la clave ya esta en el arbol, actualiza el valor asociado a la clave.
insert :: Ord k => [k] -> v -> TTree k v -> TTree k v
insert [] _ _ = E
insert [k] val E = Leaf k val
insert (k:ks) val E = Node k Nothing E (insert ks val E) E
insert [k] val (Leaf key _) | k == key = Leaf k val
insert keys@(k:ks) val (Leaf key value) | k > key = Node key (Just value) E E (insert keys val E)
                                        | k < key = Node key (Just value) (insert keys val E) E E
                                        | otherwise = Node key (Just value) E (insert ks val E) E
insert [k] val (Node key value l m r) | k == key = Node key (Just val) l m r
insert keys@(k:ks) val (Node key value l m r)   | k < key = Node key value (insert keys val l) m r
                                                | k > key = Node key value l m (insert keys val r)
                                                | otherwise = Node key value l (insert ks val m) r

-- 3)
-- Funcion parcial auxiliar maybeToValue, recibe un Maybe value y devuelve un value.
maybeToValue :: Maybe v -> v
maybeToValue (Just v) = v

-- Funcion auxiliar check, chequea los distintos casos que podemos tener
-- cuando eliminamos un nodo del arbol.
check :: TTree k v -> TTree k v
check (Node key Nothing E E E) = E                            -- E E E + Nothing
check (Node key value E E E) = Leaf key (maybeToValue value)  -- E E E + value
check (Node key Nothing l E E) = l                            -- Leaf/Node E E + Nothing
check (Node key Nothing E E r) = r                            -- E E Leaf/Node + Nothing
check (Node key Nothing (Leaf key1 value1) E (Leaf key2 value2)) = 
                                                Node key2 (Just value2) (Leaf key1 value1) E E -- Leaf E Leaf + Nothing
check (Node key Nothing node@(Node nkey nvalue nl nm nr) E (Leaf lkey lvalue)) = 
                                                Node lkey (Just lvalue) node E E  -- Node E Leaf + Nothing
check (Node key Nothing (Leaf lkey lvalue) E node@(Node nkey nvalue nl nm nr)) = 
                                                Node lkey (Just lvalue) E E node  -- Leaf E Node + Nothing
check (Node key value l m r) = Node key value l m r           

-- Funcion delete, recibe una palabra y un arbol, y borra la palabra del arbol.
delete :: Ord k => [k] -> TTree k v -> TTree k v
delete [] _  = E
delete _ E = E
delete [k] (Leaf key _) | k == key = E
delete _ leaf@(Leaf _ _) = leaf
delete [k] (Node key _ l m r) | k == key = check (Node key Nothing l m r)
delete keys@(k:ks) (Node key value l m r) | k < key = check (Node key value (delete keys l) m r)
                                          | k > key = check (Node key value l m (delete keys r))
                                          | otherwise = check (Node key value l (delete ks m) r)

-- 4) 

-- Funcion auxiliar
keysAux :: [[k]] -> [k] -> TTree k v -> [[k]]
keysAux _ _ E = []
keysAux kss ks (Leaf key value) = kss ++ [ks ++ [key]]
keysAux kss ks (Node key Nothing l m r) =
    (keysAux kss ks l) ++ keysAux kss (ks ++ [key]) m ++ (keysAux kss ks r)
keysAux kss ks (Node key value l m r) =
    (keysAux kss ks l) ++ kss ++ [ks ++ [key]] ++ (keysAux kss (ks ++ [key]) m) ++ (keysAux kss ks r)

-- Funcion keys
-- Dado un arbol, devuelve una lista con las claves del arbol ordenadas.
keys :: Eq v => TTree k v -> [[k]]
keys t = keysAux [] [] t

-- 5)

-- Funcion auxiliar
keysValuesAux :: Ord k => [([k], Maybe v)] -> [k] -> TTree k v -> [([k], Maybe v)]
keysValuesAux _ _ E = []
keysValuesAux kss ks (Leaf key value) = kss ++ [(ks++[key], Just value)]
keysValuesAux kss ks (Node key Nothing l m r) = 
    (keysValuesAux kss ks l) ++ keysValuesAux kss (ks++[key]) m ++ (keysValuesAux kss ks r)
keysValuesAux kss ks (Node key value l m r) =
    (keysValuesAux kss ks l) ++ kss ++ [(ks ++ [key], value)] ++ (keysValuesAux kss (ks++[key]) m) ++ (keysValuesAux kss ks r)

-- funcion keysValues que devuelve una lista de tuplas (k, v)
-- donde k es la clave y v el valor asociado a la clave.
keysValues :: Ord k => TTree k v -> [([k], Maybe v)]
keysValues t = keysValuesAux [] [] t

-- Clase Dic
class Dic k v d | d -> k v where
    empty :: d
    insertar :: Ord k => k -> v -> d -> d
    buscar :: Ord k => k -> d -> Maybe v
    borrar :: Ord k => k -> d -> d
    claves :: Ord k => d -> [(k, Maybe v)]

-- Instancia de Dic para TTree
instance Ord k => Dic [k] v (TTree k v) where
    empty = E
    insertar = insert
    buscar = search
    borrar = delete
    claves = keysValues
