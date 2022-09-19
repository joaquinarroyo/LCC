module Eval3
  ( eval
  , State
  )
where

import           AST
import qualified Data.Map.Strict               as M
import           Data.Strict.Tuple

-- Estados
type State = (M.Map Variable Int, Integer)

-- Estado nulo
initState :: State
initState = (M.empty, 0)

-- Busca el valor de una variable en un estado
lookfor :: Variable -> State -> Either Error Int
lookfor v (s, _) = case M.lookup v s of
                    Just x -> Right x
                    _ -> Left UndefVar

-- Cambia el valor de una variable en un estado
update :: Variable -> Int -> State -> State
update x v (s, w) = (M.insert x v s, w)

-- Suma un costo dado al estado
addWork :: Integer -> State -> State
addWork n (s, w) = (s, w+n) 

-- Evalua un programa en el estado nulo
eval :: Comm -> Either Error State
eval p = stepCommStar p initState

-- Evalua multiples pasos de un comnado en un estado,
-- hasta alcanzar un Skip
stepCommStar :: Comm -> State -> Either Error State
stepCommStar Skip s = return s
stepCommStar c    s = do
  (c' :!: s') <- stepComm c s
  stepCommStar c' s'

-- Evalua un paso de un comando en un estado dado
stepComm :: Comm -> State -> Either Error (Pair Comm State)
stepComm (Let v x) s = case evalExp x s of
                          Right (n :!: s') -> Right (Skip :!: (update v n s'))
                          Left e -> Left e
stepComm (IfThenElse b c1 c2) s = case evalExp b s of
                                    Right (True :!: s') -> Right (c1 :!: s')
                                    Right (False :!: s') -> Right (c2 :!: s')
                                    Left e -> Left e
stepComm (While b c) s = case evalExp b s of
                          Right (True :!: s') -> Right (Seq c (While b c) :!: s')
                          Right (False :!: s') -> Right (Skip :!: s')
                          Left e -> Left e
stepComm (Seq Skip c) s = Right (c :!: s)
stepComm (Seq c cs) s = case stepComm c s of
                          Right (c' :!: s') -> stepComm (Seq c' cs) s'
                          Left e -> Left e

-- Evalua una expresion
evalExp :: Exp a -> State -> Either Error (Pair a State)
evalExp (Const x) s = Right (x :!: (addWork 0 s))
evalExp (Var v) s = case lookfor v s of
                      Right x -> Right (x :!: (addWork 0 s))
                      Left e -> Left e
evalExp (UMinus e) s = case evalExp e s of
                        Right (x :!: s') -> Right (-x :!: (addWork 1 s'))
                        Left e -> Left e
evalExp (Plus x y) s = evalExp' x y s 2 (+)
evalExp (Minus x y) s = evalExp' x y s 2 (-)
evalExp (Times x y) s = evalExp' x y s 3 (*)
evalExp (Div x y) s = case evalExp x s of
                        Right (x' :!: s1) ->  case evalExp y s1 of
                                                Right (0 :!: _) -> Left DivByZero
                                                Right (y' :!: s2) -> Right (x' `div` y' :!: (addWork 3 s2))
                                                Left e1 -> Left e1
                        Left e2 -> Left e2
evalExp (ECond b x y) s = case evalExp b s of
                            Right (True :!: s') -> evalExp x (addWork 1 s')
                            Right (False :!: s') -> evalExp y (addWork 1 s')
                            Left e -> Left e
evalExp BTrue s = Right (True :!: s)
evalExp BFalse s = Right (False :!: s)
evalExp (Lt x y) s = evalExp' x y s 2 (<)
evalExp (Gt x y) s = evalExp' x y s 2 (>)
evalExp (Eq x y) s = evalExp' x y s 2 (==)
evalExp (NEq x y) s = evalExp' x y s 2 (/=)
evalExp (And x y) s = evalExp' x y s 2 (&&)
evalExp (Or x y) s = evalExp' x y s 2 (||)
evalExp (Not b) s = case evalExp b s of
                      Right (x :!: s') -> Right (x :!: (addWork 1 s'))
                      Left e -> Left e

-- Evaluador auxiliar de expresiones, ademas recibe el trabajo de aplicarle el operador
-- a las dos expresiones recibidas y lo agrega al estado.
evalExp' :: Exp a -> Exp a -> State -> Integer -> (a -> a -> b) -> Either Error (Pair b State)
evalExp' x y s w op = case evalExp x s of
                        Right (x' :!: s1) -> case evalExp y s1 of
                                              Right (y' :!: s2) -> Right ((op x' y') :!: (addWork w s2))
                                              Left e1 -> Left e1
                        Left e2 -> Left e2