import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

newtype ReaderM m e a = R {runR :: e -> m a}

instance Monad m => Functor (ReaderM m e) where
    fmap = liftM

instance Monad m => Applicative (ReaderM m e) where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (ReaderM m e) where
    return x = R (\e -> return x) -- me salio
    p >>= f = R (\e -> do x <- runR p e
                          runR (f x) e) -- no me salio

ask :: Monad m => ReaderM m e e 
ask = R (\e -> return e) -- me salio

local :: Monad m => e -> ReaderM m e a -> ReaderM m e a
local e p = R (\_ -> runR p e) -- no me salio
              
data Prop = Var String | Cons Bool | And Prop Prop | Not Prop | Def String Prop Prop

type Env = [(String, Bool)]

data Result a = UndefVar String | Res a deriving Show

instance Functor Result where
    fmap = liftM

instance Applicative Result where
    pure  = return
    (<*>) = ap

instance Monad Result where -- me salio
    return x = Res x 
    m >>= f = case m of
                UndefVar s -> UndefVar s
                Res a -> f a

find :: String -> [(String, Bool)] -> ReaderM Result Env Bool -- auxiliar
find s [] = undef s
find s ((k, v):xs) = if s == k then return v else find s xs

undef :: String -> ReaderM Result Env a -- me salio
undef s = R (\e -> UndefVar s)

eval :: Prop -> ReaderM Result Env Bool -- me salio
eval (Var s) = do e <- ask
                  find s e
eval (Cons b) = return b
eval (And b1 b2) = do v1 <- eval b1
                      v2 <- eval b2
                      return (v1 && v2) 
eval (Def s b1 b2) = do v1 <- eval b1
                        local [(s, v1)] (eval b2)
eval (Not b) = do v <- eval b
                  return (not v)

env = [("x", True), ("y", True)]

app :: Prop -> Env -> Result Bool -- me salio
app p e = runR (eval p) e


--------------------------------------------
data B a = B (a -> Bool)

class Contravariant f where
    contramap :: (a -> b) -> f b -> f a

instance Contravariant B where
    contramap f (B g) = B (g . f)

---------------------------------------------
