import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

type Env = [(String,Bool)]

newtype MonadWriter a = MW { runMW :: Env -> (a, String, Int) }

instance Functor MonadWriter where
    fmap = liftM

instance Applicative MonadWriter where
    pure  = return
    (<*>) = ap

instance Monad MonadWriter where
  return x = MW (\env -> (x, "", 0))
  (MW f) >>= g = MW (\env -> let (x, s1, n1) = f env
                                 (y, s2, n2) = runMW (g x) env
                             in (y, s1 ++ s2, n1 + n2))

get :: MonadWriter Env
get = MW (\env -> (env, "", 0))

local :: (Env -> Env) -> MonadWriter a -> MonadWriter a
local f m = MW (\env -> runMW m (f env))

putTrace :: String -> MonadWriter ()
putTrace s = MW (\env -> ((), s, 0))

add :: MonadWriter ()
add = MW (\env -> ((), "", 1))

data Expr = Var String | T | F | And Expr Expr | Not Expr | Let String Expr Expr deriving Show

eval :: Expr -> MonadWriter Bool
eval T = return True
eval F = return False
eval b@(And b1 b2) = do b1' <- eval b1
                        b2' <- eval b2
                        putTrace (show b ++ " --> " ++ show (b1' && b2') ++ "\n") 
                        add
                        return (b1' && b2')
eval b@(Not b1) = do b' <- eval b1
                     putTrace (show b ++ " --> " ++ show (not b') ++ "\n")
                     add 
                     return (not b')
eval b@(Let s b1 b2) = do b1' <- eval b1
                          b2' <- local ((++)[(s, b1')]) (eval b2)
                          putTrace (show b ++ " --> " ++ show (b2') ++ "\n")
                          add
                          return b2'
eval (Var s) = do e <- get
                  v <- search s e
                  return v

search :: String -> Env -> MonadWriter Bool
search s [] = return False
search s ((s',b):xs) = if s == s' then return b else search s xs

ver :: Expr -> IO ()
ver b = let (b', s, n) = runMW (eval b) []
        in do putStrLn ("La evaluacion dio como resultado: " ++ (show b'))
              putStrLn "Pasos: "
              putStrLn s
              putStrLn ("Numero de pasos: " ++ show n)

                