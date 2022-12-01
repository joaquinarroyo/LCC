module Eval2
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

-- Mónada estado, con manejo de errores
newtype StateError a =
  StateError { runStateError :: Env -> Either Error (Pair a Env) }

-- Para calmar al GHC
instance Functor StateError where
  fmap = liftM

instance Applicative StateError where
  pure  = return
  (<*>) = ap

-- Ejercicio 2.a: Dar una instancia de Monad para StateError:
instance Monad StateError where
  return x = StateError (\s -> Right (x :!: s))
  m >>= f = StateError (\s -> case runStateError m s of
                                Right (x :!: s) -> runStateError (f x) s
                                Left e -> Left e)

-- Ejercicio 2.b: Dar una instancia de MonadError para StateError:
instance MonadError StateError where
  throw e = StateError (\_ -> Left e)

-- Ejercicio 2.c: Dar una instancia de MonadState para StateError:
instance MonadState StateError where
  lookfor v = StateError (\s -> case lookfor' v s of
                                  Just x -> return (x :!: s)
                                  Nothing -> Left UndefVar)
    where lookfor' v s = M.lookup v s
  update v i = StateError (\s -> Right (() :!: update' v i s)) where update' = M.insert

-- Ejercicio 2.d: Implementar el evaluador utilizando la monada StateError.
-- Evalua un programa en el estado nulo
eval :: Comm -> Either Error Env
eval c = case runStateError (stepCommStar c) initEnv of
          Right (x :!: s) -> Right s
          Left e -> Left e

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: (MonadState m, MonadError m) => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm :: (MonadState m, MonadError m) => Comm -> m Comm
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
evalExp :: (MonadState m, MonadError m) => Exp a -> m a
evalExp (Const x)   = return x
evalExp (Var v)     = lookfor v
evalExp (UMinus e)  = do e' <- evalExp e
                         return (-e')
evalExp (Plus x y)  = evalExpAux (+) x y
evalExp (Minus x y) = evalExpAux (-) x y
evalExp (Times x y) = evalExpAux (*) x y
evalExp (Div x y)   = do v1 <- evalExp x
                         v2 <- evalExp y
                         if v2 == 0
                            then throw DivByZero
                            else return (div v1 v2)
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

evalExpAux :: (MonadState m, MonadError m) => (a -> a -> b) -> Exp a -> Exp a -> m b
evalExpAux o x y = do v1 <- evalExp x
                      v2 <- evalExp y
                      return (o v1 v2)

