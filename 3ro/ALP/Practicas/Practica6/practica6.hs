import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

-- 3)
newtype State s a = St {runState :: s -> (a, s)}

instance Functor (State s) where
    fmap = liftM

instance Applicative (State s) where
    pure = return
    (<*>) = ap 

instance Monad (State s) where
    return x = St (\s -> (x , s))
    (St h) >>= f = St (\s -> let (x , s') = h s
                             in runState (f x ) s')

set :: s -> State s ()
set s = St (\_ -> ((), s))

get :: State s s
get = St (\s -> (s, s)) 

-- 4)
data Tree a = Leaf a | Branch (Tree a) (Tree a) deriving Show

instance Functor Tree where
    fmap f (Leaf x) = Leaf (f x)
    fmap f (Branch l r) = Branch (fmap f l) (fmap f r)

t = Branch (Branch (Leaf 4) (Leaf 3)) (Leaf 2)

numTree :: Tree a -> Tree Int
numTree t = fst (mapTreeNro update t 0)
    where update a n = (n, n + 1)

mapTreeNro :: (a -> Int -> (b, Int)) -> Tree a -> Int -> (Tree b, Int)
mapTreeNro f (Leaf x) n = (Leaf y, n')
    where (y, n') = f x n
mapTreeNro f (Branch l r) n = (Branch l' r', n'')
    where (l', n') = mapTreeNro f l n
          (r', n'') = mapTreeNro f r n'

mapTreeM :: (a -> State s b) -> Tree a -> State s (Tree b)
mapTreeM f (Leaf x) = do b <- f x
                         return (Leaf b)
mapTreeM f (Branch l r) = do l' <- mapTreeM f l
                             r' <- mapTreeM f r
                             return (Branch l' r')


