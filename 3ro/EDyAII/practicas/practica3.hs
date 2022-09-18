module Practica3 where
import Data.Char ( isDigit, digitToInt, isNumber )

-- linea = borrar (0, "aabaaa") 

-- 1
type Color = (Float, Float, Float)

mezclar :: Color -> Color -> Color
mezclar (x1, y1, z1) (x2, y2, z2) = ( (x1 + x2) / 2,  (y1 + y2) / 2, (z1 + z2) / 2)

-- 2

type Linea = (Int, String)

-- iniciar linea
vacia :: Linea
vacia = (0, "")

moverDer :: Linea -> Linea
moverDer (p, s) | p < length s = (p+1, s)
                | otherwise = (p, s)

moverIzq :: Linea -> Linea
moverIzq (p, s) | p > 0 = (p-1, s)
                | otherwise = (p, s)

moverIni :: Linea -> Linea
moverIni (_, s) = (0, s)

moverFin :: Linea -> Linea
moverFin (_, s) = (length s, s)

insertar :: Char -> Linea -> Linea
insertar c (p, s) = (p+1, take p s ++ [c] ++ drop p s)

borrar :: Linea -> Linea
borrar (p, s) | p == 0 = (0, s)
              | otherwise = (p-1, take (p-1) s ++ drop p s)

-- 3
data CList a = EmptyCL | CUnit a | Consnoc a (CList a) a

instance Show a => Show (CList a) where
    show EmptyCL = "EmptyCL"
    show (CUnit a) = "CUnit " ++ show a
    show (Consnoc a b c) = "Consnoc " ++ show a ++ " " ++ show b ++ " " ++ show c

headCL :: CList a -> CList a
headCL EmptyCL = EmptyCL
headCL (CUnit x) = CUnit x
headCL (Consnoc x1 _ x3) = CUnit x1

tailCL :: CList a -> CList a
tailCL EmptyCL = EmptyCL
tailCL (CUnit x) = EmptyCL
tailCL (Consnoc _ x _) = x

isEmptyCL :: CList a -> Bool
isEmptyCL EmptyCL = True
isEmptyCL _ = False

isCUnit :: CList a -> Bool
isCUnit (CUnit _) = True
isCUnit _ = False

reverseCList :: CList a -> CList a
reverseCList EmptyCL = EmptyCL
reverseCList (CUnit x) = CUnit x
reverseCList (Consnoc x1 list x2) = Consnoc x2 (reverseCList list) x1

initsClist :: CList a -> CList a
initsClist EmptyCL = EmptyCL
initsClist (CUnit x) = CUnit x
initsClist (Consnoc x1 list x2) = Consnoc x1 (initsClist list) x2

lastsClist :: CList a -> CList a
lastsClist EmptyCL = EmptyCL
lastsClist (CUnit x) = CUnit x
lastsClist (Consnoc x1 list x2) = Consnoc x2 (lastsClist list) x1

concatCList :: CList a -> CList a -> CList a
concatCList EmptyCL xs = xs
concatCList (CUnit x) xs = Consnoc x xs x
concatCList (Consnoc x1 list1 y1) xs = Consnoc x1 (concatCList list1 xs) y1

flatCList :: CList (CList a) -> CList a
flatCList EmptyCL = EmptyCL
flatCList (CUnit x) = x
flatCList (Consnoc x list y) = concatCList (concatCList x (flatCList list)) y

-- 4

data Exp = Lit Int | Add Exp Exp | Sub Exp Exp | Prod Exp Exp | Div Exp Exp
instance Show Exp where
    show (Lit x) = show x
    show (Add exp1 exp2) = "(Add " ++ show exp1 ++ " " ++ show exp2  ++ ")"
    show (Sub exp1 exp2) = "(Sub " ++ show exp1 ++ " " ++ show exp2  ++ ")"
    show (Prod exp1 exp2) = "(Prod " ++ show exp1 ++ " " ++ show exp2  ++ ")"
    show (Div exp1 exp2) = "(Div " ++ " " ++ show exp2  ++ ")"

eval :: Exp -> Int
eval (Lit x) = x
eval (Add exp1 exp2) = eval exp1 + eval exp2
eval (Sub exp1 exp2) = eval exp1 - eval exp2
eval (Prod exp1 exp2) = eval exp1 * eval exp2
eval (Div exp1 exp2) | eval exp2 == 0 = error "Division por 0"
                     | otherwise = div (eval exp1) (eval exp2)

-- 5
type Pila = [Exp]

operador :: String -> Exp -> Exp -> Exp
operador "-" = Sub
operador "+" = Add
operador "/" = Div
operador "*" = Prod
operador _ = error ""

parseNpr :: String -> Exp
parseNpr = parseNprAux []

parseNprAux :: Pila -> String -> Exp
parseNprAux [] [] = error "Expresion mal formada"
parseNprAux stack [] | length stack == 1 = head stack
                     | otherwise = error "Expresion mal formada"
parseNprAux stack s | isNumber' x = parseNprAux (Lit (read x) : stack) xs
                    | x == " " = parseNprAux stack xs
                    | otherwise = parseNprAux (operador x (stack !! 1) (head stack) : drop 2 stack) xs
    where
        (x, xs) = getFirst s

isNumber' :: String -> Bool
isNumber' = foldr ((&&) . isDigit) True

getFirst :: String -> (String, String)
getFirst = getFirstAux []

getFirstAux :: String -> String -> (String, String)
getFirstAux s [] = (s, [])
getFirstAux s (' ':xs) = (reverse s, xs)
getFirstAux s (x:xs) = getFirstAux (x:s) xs

evalNpr :: String -> Int
evalNpr expr = eval (parseNpr expr)

-- 6

seval :: Exp -> Maybe Int
seval (Lit x) = Just x
seval (Add expr1 expr2) = Just (eval expr1 + eval expr2)
seval (Sub expr1 expr2) = Just (eval expr1 - eval expr2)
seval (Prod expr1 expr2) = Just (eval expr1 * eval expr2)
seval (Div expr1 expr2) | eval expr2 == 0 = Nothing
                        | otherwise = Just (div (eval expr1) (eval expr2))
