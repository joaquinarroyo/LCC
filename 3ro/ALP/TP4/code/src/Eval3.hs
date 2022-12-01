module Eval3
  ( eval
  , Env
  )
where

import           AST
import           Monads
import qualified Data.Map.Strict               as M
import           Data.Maybe
import           Data.Strict.Tuple
import           Control.Monad                  ( liftM
                                                , ap
                                                )

-- Entornos
type Env = M.Map Variable Int

-- Entorno nulo
initEnv :: Env
initEnv = M.empty

initTrace :: Trace
initTrace = ""

-- Ejercicio 3.a: Proponer una nueva monada que  
-- lleve una traza de ejecución (además de manejar errores y estado).
-- y dar su instancia de mónada. Llamarla |StateErrorTrace|. 
-- COMPLETAR
newtype StateErrorTrace a = StateErrorTrace { runStateErrorTrace :: Env -> Either Error (Pair a Env, Trace) }

-- Recuerde agregar las siguientes instancias para calmar al GHC:
instance Functor StateErrorTrace where
  fmap = liftM

instance Applicative StateErrorTrace where
  pure  = return
  (<*>) = ap

-- Ejercicio 3.b: Resolver en Monad.hs

instance Monad StateErrorTrace where
  return x = StateErrorTrace (\s -> Right (x :!: s, initTrace))
  m >>= f  = StateErrorTrace (\s -> case runStateErrorTrace m s of
                                        Right (x' :!: s', t') -> case runStateErrorTrace (f x') s' of
                                                                    Right (x'' :!: s'', t'') -> Right (x'':!: s'', t' ++ t'')
                                                                    (Left e')               -> Left e'
                                        (Left e)              -> Left e
                              )

-- Ejercicio 3.c: Dar una instancia de MonadTrace para StateErrorTrace.
-- COMPLETAR
instance MonadTrace StateErrorTrace where
  add e = StateErrorTrace (\s -> Right ("" :!: s, e))

-- Ejercicio 3.d: Dar una instancia de MonadError para StateErrorTrace.
-- COMPLETAR
instance MonadError StateErrorTrace where
  throw e = StateErrorTrace (\_ -> Left e)

-- Ejercicio 3.e: Dar una instancia de MonadState para StateErrorTrace.
-- COMPLETAR
instance MonadState StateErrorTrace where
  lookfor v = StateErrorTrace (\s -> case lookfor' v s of
                                        Just x -> return (x :!: s, initTrace)
                                        Nothing -> Left UndefVar)
    where lookfor' v s = M.lookup v s
  update v i = StateErrorTrace (\s -> Right (() :!: update' v i s, initTrace))
    where update' = M.insert

-- Ejercicio 3.f: Implementar el evaluador utilizando la monada StateErrorTrace.
-- Evalua un programa en el estado nulo
eval :: Comm -> Either Error (Env, Trace)
eval c = case runStateErrorTrace (stepCommStar c) initEnv of
          Right (x :!: s, t) -> Right (s, t)
          Left e -> Left e

-- Evalua multiples pasos de un comando, hasta alcanzar un Skip
stepCommStar :: (MonadState m, MonadError m, MonadTrace m) => Comm -> m ()
stepCommStar Skip = return ()
stepCommStar c    = stepComm c >>= \c' -> stepCommStar c'

-- Evalua un paso de un comando
stepComm :: (MonadState m, MonadError m, MonadTrace m) => Comm -> m Comm
stepComm c@(Let v (Const x)) = do update v x
                                  add (v ++ " -> " ++ show x ++ "\n")
                                  return Skip
stepComm c@(Let v x) = do add (v ++ " -> ")
                          i <- evalExp x
                          update v i
                          return Skip
stepComm c@(IfThenElse b c1 c2) = do b' <- evalExp b
                                     if b' then return c1
                                           else return c2
stepComm c@(While b c1) = do b' <- evalExp b
                             if b'
                             then return (Seq c1 (While b c1))
                             else return Skip
stepComm c@(Seq Skip c1) = return c1
stepComm c@(Seq c1 cs) = do c' <- stepComm c1
                            stepComm (Seq c' cs)

-- Evalua una expresion 
evalExp :: (MonadState m, MonadError m, MonadTrace m) => Exp a -> m a
evalExp (Const x) = return x
evalExp (Var v) = do n <- lookfor v 
                     return n  
evalExp e@(UMinus e1) = do e' <- evalExp e1
                           add (show e ++ " -> " ++ show (-e') ++ "\n")
                           return (-e')
evalExp e@(Plus x y) = evalExpAux (+) e x y
evalExp e@(Minus x y) = evalExpAux (-) e x y
evalExp e@(Times x y) = evalExpAux (*) e x y
evalExp e@(Div x y) = do v1 <- evalExp x
                         v2 <- evalExp y
                         if v2 == 0
                         then throw DivByZero
                         else do add (show e ++ " -> " ++ show (v1 `div` v2) ++ "\n")
                                 return (v1 `div` v2)
evalExp BTrue = return True
evalExp BFalse = return False
evalExp e@(Lt x y) = evalExpAux (<) e x y
evalExp e@(Gt x y) = evalExpAux (>) e x y
evalExp e@(Eq x y) = evalExpAux (==) e x y
evalExp e@(NEq x y) = evalExpAux (/=) e x y
evalExp e@(And x y) = evalExpAux (&&) e x y
evalExp e@(Or x y) = evalExpAux (||) e x y
evalExp e@(Not b) = do b' <- evalExp b
                       add (show e ++ " -> " ++ show (not b'))
                       return (not b')

evalExpAux :: (Show b, Show c, MonadState m, MonadError m, MonadTrace m) => (a -> a -> b) -> Exp c -> Exp a -> Exp a -> m b
evalExpAux o e e1 e2 = do v1 <- evalExp e1
                          v2 <- evalExp e2
                          add (show e ++ " -> " ++ show (o v1 v2) ++ "\n")
                          return (o v1 v2)

