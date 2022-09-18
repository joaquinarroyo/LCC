module Eval1
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
lookfor :: Variable -> State -> Int
lookfor v s = case M.lookup v s of
                   Just x -> x

-- Cambia el valor de una variable en un estado
update :: Variable -> Int -> State -> State
update = M.insert

-- Evalua un programa en el estado nulo
eval :: Comm -> State
eval p = stepCommStar p initState

-- Evalua multiples pasos de un comnado en un estado,
-- hasta alcanzar un Skip
stepCommStar :: Comm -> State -> State
stepCommStar Skip s = s
stepCommStar c    s = Data.Strict.Tuple.uncurry stepCommStar $ stepComm c s

-- Evalua un paso de un comando en un estado dado
stepComm :: Comm -> State -> Pair Comm State
stepComm (Let v x) s = Skip :!: (update v (evalExp x s) s)
stepComm (IfThenElse b c1 c2) s = if evalExp b s
                                  then c1 :!: s
                                  else c2 :!: s
stepComm (While b c) s = if evalExp b s
                         then Seq c (While b c) :!: s
                         else Skip :!: s
stepComm (Seq Skip c) s = c :!: s
stepComm (Seq c cs) s = let newC :!: newS = stepComm c s
                        in stepComm (Seq newC cs) newS

-- Evalua una expresion
evalExp :: Exp a -> State -> a
evalExp (Const x) s = x
evalExp (Var v) s = lookfor v s
evalExp (UMinus e) s = -(evalExp e s)
evalExp (Plus x y) s = evalExp x s + evalExp y s
evalExp (Minus x y) s = evalExp x s - evalExp y s
evalExp (Times x y) s = evalExp x s * evalExp y s
evalExp (Div x y) s = evalExp x s `div` evalExp y s
evalExp (ECond b x y) s = if evalExp b s
                          then evalExp x s
                          else evalExp y s
evalExp BTrue s = True
evalExp BFalse s = False
evalExp (Lt x y) s = evalExp x s < evalExp y s
evalExp (Gt x y) s = evalExp x s > evalExp y s
evalExp (Eq x y) s = evalExp x s == evalExp y s
evalExp (NEq x y) s = evalExp x s /= evalExp y s
evalExp (And x y) s = evalExp x s && evalExp y s
evalExp (Or x y) s = evalExp x s || evalExp y s
evalExp (Not b) s = not (evalExp b s)