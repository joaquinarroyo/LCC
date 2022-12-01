import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))
import Data.Char

newtype Parser i o = P {runP :: i -> Maybe (o, i)}

instance Functor (Parser i) where
    fmap = liftM

instance Applicative (Parser i) where
    pure  = return
    (<*>) = ap

instance Monad (Parser i) where
    return x = P (\s -> return (x, s))
    (P h) >>= f = P (\s -> case h s of
                            Nothing -> Nothing
                            Just (x, s') -> runP (f x) s')

item :: Parser String Char
item = P (\s -> case s of
                 [] -> Nothing
                 (x:xs) -> Just (x, xs))

failure :: Parser i o
failure = P (\s -> Nothing)

word :: String -> Parser String String
word [] = P (\s -> Just ("", s))
word (x:xs) = do c <- item
                 if c == x
                 then do cs <- word xs
                         return (c:cs)
                 else failure

parse :: Show o => Parser String o -> String -> IO ()
parse p s = do content <- readFile s
               case runP p content of
                 Nothing -> putStrLn "No parse"
                 Just (x, xs) -> writeFile s xs
