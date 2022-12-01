module Eval1
  ( eval
  , Env
  )
where

import           AST
import           Monads
import qualified Data.Map.Strict               as M
import           Data.Maybe
import           Prelude                 hiding ( fst
                                                , snd
                                                )
import           Data.Strict.Tuple
import           Control.Monad                  ( liftM
                                                , ap
                                                )

-- Entornos
type Env = M.Map Variable Int

-- Entorno nulo
initEnv :: Env
initEnv = M.empty

-- Mónada estado
newtype State a = State { runState :: Env -> Pair a Env }

instance Monad State where
  return x = State (\s -> (x :!: s))
  m >>= f = State (\s -> let (v :!: s') = runState m s in runState (f v) s')

-- Para calmar al GHC
instance Functor State where
  fmap = liftM

instance Applicative State where
  pure  = return
  (<*>) = ap

instance MonadState State where
  lookfor v = State (\s -> (lookfor' v s :!: s))
    where lookfor' v s = fromJust $ M.lookup v s
  update v i = State (\s -> (() :!: update' v i s)) 
    where update' = M.insert

-- Ejercicio 1.b: Implementar el evaluador utilizando la monada State

-- Evalua un programa en el estado nulo
eval :: Comm -> Env
eval p = snd (runState (stepCommStar p) initEnv)

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: MonadState m => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm :: MonadState m => Comm -> m Comm
stepComm (Let v x) = do i <- evalExp x
                        update v i
                        return Skip
stepComm (IfThenElse b c1 c2) = do b' <- evalExp b
                                   if b'
                                     then return c1
                                     else return c2
stepComm (While b c) = do b' <- evalExp b
                          if b'
                            then return (Seq c (While b c))
                            else return Skip
stepComm (Seq Skip c) = return c
stepComm (Seq c cs) = do c' <- stepComm c
                         stepComm (Seq c' cs)

-- Evalua una expresion
evalExp :: MonadState m => Exp a -> m a
evalExp (Const x)   = return x
evalExp (Var v)     = lookfor v
evalExp (UMinus e)  = do e' <- evalExp e
                         return (-e')
evalExp (Plus x y)  = evalExpAux (+) x y
evalExp (Minus x y) = evalExpAux (-) x y
evalExp (Times x y) = evalExpAux (*) x y
evalExp (Div x y)   = evalExpAux (div) x y
evalExp BTrue       = return True
evalExp BFalse      = return False
evalExp (Lt x y)    = evalExpAux (<) x y
evalExp (Gt x y)    = evalExpAux (>) x y
evalExp (Eq x y)    = evalExpAux (==) x y
evalExp (NEq x y)   = evalExpAux (/=) x y
evalExp (And x y)   = evalExpAux (&&) x y
evalExp (Or x y)    = evalExpAux (||) x y
evalExp (Not b)     = do b' <- evalExp b
                         return (not b')

evalExpAux :: MonadState m => (a -> a -> b) -> Exp a -> Exp a -> m b
evalExpAux o x y = do v1 <- evalExp x
                      v2 <- evalExp y
                      return (o v1 v2)


