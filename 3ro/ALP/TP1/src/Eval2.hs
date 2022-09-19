module Eval2
  ( eval
  , State
  )
where

import           AST
import qualified Data.Map.Strict               as M
import           Data.Strict.Tuple

-- Estados
type State = M.Map Variable Int

-- Estado nulo
initState :: State
initState = M.empty

-- Busca el valor de una variable en un estado
lookfor :: Variable -> State -> Either Error Int
lookfor v s = case M.lookup v s of
                   Just x -> Right x
                   _ -> Left UndefVar

-- Cambia el valor de una variable en un estado
update :: Variable -> Int -> State -> State
update = M.insert

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
                        Right n -> Right (Skip :!: update v n s)
                        Left e -> Left e
stepComm (IfThenElse b c1 c2) s = case evalExp b s of
                                    Right True -> Right (c1 :!: s)
                                    Right False -> Right (c2 :!: s)
                                    Left e -> Left e
stepComm (While b c) s = case evalExp b s of
                          Right True -> Right (Seq c (While b c) :!: s)
                          Right False -> Right (Skip :!: s)
                          Left e -> Left e
stepComm (Seq Skip c) s = Right (c :!: s)
stepComm (Seq c cs) s = case stepComm c s of
                          Right (c' :!: s') -> stepComm (Seq c' cs) s'
                          Left e -> Left e

-- Evalua una expresion
evalExp :: Exp a -> State -> Either Error a
evalExp (Const x) s = Right x
evalExp (Var v) s = case lookfor v s of
                      Right x -> Right x
                      Left e -> Left e
evalExp (UMinus e) s = case evalExp e s of
                        Right x -> Right (-x)
                        Left e -> Left e
evalExp (Plus x y) s = evalExp' x y s (+)
evalExp (Minus x y) s = evalExp' x y s (-)
evalExp (Times x y) s = evalExp' x y s (*)
evalExp (Div x y) s = case evalExp x s of
                        Right x' ->  case evalExp y s of
                                      Right 0  -> Left DivByZero
                                      Right y' -> Right (x' `div` y')
                                      Left e1  -> Left e1
                        Left e2 -> Left e2
evalExp (ECond b x y) s = case evalExp b s of
                            Right True -> evalExp x s
                            Right False -> evalExp y s
                            Left e -> Left e
evalExp BTrue s = Right True
evalExp BFalse s = Right False
evalExp (Lt x y) s = evalExp' x y s (<)
evalExp (Gt x y) s = evalExp' x y s (>)
evalExp (Eq x y) s = evalExp' x y s (==)
evalExp (NEq x y) s = evalExp' x y s (/=)
evalExp (And x y) s = evalExp' x y s (&&)
evalExp (Or x y) s = evalExp' x y s (||)
evalExp (Not b) s = case evalExp b s of
                      Right x -> Right x
                      Left e -> Left e

-- Evaluador auxiliar de expresiones, recibe un operador y se lo aplica
-- a las dos expresiones recibidas.
evalExp' :: Exp a -> Exp a -> State -> (a -> a -> b) -> Either Error b
evalExp' x y s op = case evalExp x s of
                      Right x' ->  case evalExp y s of
                                    Right y' -> Right (op x' y')
                                    Left e1 -> Left e1
                      Left e2 -> Left e2