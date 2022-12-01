import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))

newtype Acum a = A (a, Int) deriving Show
runAcum :: Acum a -> (a, Int)
runAcum (A x) = x

instance Functor Acum where
    fmap = liftM

instance Applicative Acum where
    pure  = return
    (<*>) = ap

instance Monad Acum where
    return x = A (x, 0)
    A (x, n) >>= f = let A (x', n') = f x
                     in A (x', n + n')

get :: Acum String
get = A ("ASD", 1)

put :: Int -> Acum ()
put x = A ((), x)

asd :: Acum String
asd = do x <- get
         put (length x)
         return x

-----------------------------------------------------------------------
newtype Parser i o = P {runP :: i -> Maybe (o, i)}

instance Functor (Parser i) where
    fmap = liftM

instance Applicative (Parser i) where
    pure  = return
    (<*>) = ap

instance Monad (Parser i) where
    return x = P (\i -> Just (x, i))
    p >>= f = P (\i -> case runP p i of
                         Nothing -> Nothing
                         Just (x, i') -> runP (f x) i')

item :: Parser String Char
item = P (\i -> case i of
                  [] -> Nothing
                  (x:xs) -> Just (x, xs))

failure :: Parser i o
failure = P (\i -> Nothing)

word :: String -> Parser String String
word [] = return []
word (x:xs) = do c <- item
                 if c == x
                 then do cs <- word xs
                         return (c:cs)
                 else failure

parse :: Parser String String -> String -> (String, String)
parse p i = case runP p i of
              Nothing -> ("", i)
              Just (x, i') -> (x, i')
               
               

-- ej
-- parse (word "hola") "hola mundo"

