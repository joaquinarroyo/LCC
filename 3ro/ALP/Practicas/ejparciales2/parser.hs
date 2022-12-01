import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))
import Data.Char

newtype Parser2 a = P {runP :: String -> Maybe (String, a)}

instance Functor Parser2 where
    fmap = liftM

instance Applicative Parser2 where
    pure  = return
    (<*>) = ap

instance Monad Parser2 where
    return x = P (\s -> return (s, x))
    (P h) >>= f = P (\s -> case h s of
                               Nothing -> Nothing
                               Just (s', x) -> runP (f x) s')

(++++) :: Parser2 a -> Parser2 a -> Parser2 a
p1 ++++ p2 = P (\s -> case runP p1 s of
                        Nothing -> runP p2 s
                        r -> r)

item :: Parser2 Char
item = P (\s -> case s of
                 [] -> Nothing
                 (x:xs) -> Just (xs, x))

falla :: Parser2 a
falla = P (\s -> Nothing)

cadena :: String -> Parser2 String
cadena [] = P (\s -> return (s, ""))
cadena (x:xs) = do c <- item
                   if c == x
                   then do cs <- cadena xs
                           return (c:cs)
                   else falla

parserInt :: Parser2 String
parserInt = do c <- item
               if isDigit c
               then do cs <- parserInt
                       return (c:cs)
               else falla
            ++++
            return ""

parserBase :: Parser2 [Int]
parserBase = (do cadena "{}"
                 return [])
               ++++
              (do cadena "{"
                  i <- parserInt
                  cadena "}"
                  return [read i])
              

parseSet :: Parser2 [Int]
parseSet = (do b1 <- parserBase
               cadena "U"
               b2 <- parseSet
               return (b1 ++ b2))
            ++++
            parserBase

parse :: Parser2 a -> String -> Maybe (String, a)
parse p s = runP p s

-------

data M m a = Mk (m (Maybe a))

runMk :: M m a -> m (Maybe a)
runMk (Mk x) = x

instance Monad m => Functor (M m) where
    fmap = liftM

instance Monad m => Applicative (M m) where
    pure = return
    (<*>) = ap

instance Monad m => Monad (M m) where
    return x = Mk (return (Just x))
    (Mk x) >>= f = Mk (do r <- x
                          case r of
                            Nothing -> return Nothing
                            Just x' -> runMk (f x'))

throw :: Monad m => M m a
throw = Mk (return Nothing)

data StInt a = St (Int -> (a, Int))

runSt :: StInt a -> Int -> (a, Int)
runSt (St h) i = h i

instance Functor StInt where
    fmap = liftM

instance Applicative StInt where
    pure = return
    (<*>) = ap

instance Monad StInt where
    return x = St (\i -> (x, i))
    (St h) >>= f = St (\i -> let (x, i') = h i
                             in runSt (f x) i')


type N a = M StInt a

get :: N Int
get = Mk (St (\i -> (Just i, i)))

put :: Int -> N ()
put i = Mk (St (\i' -> (Just (), i)))

data Expr = Var | Con Int | Let Expr Expr | Add Expr Expr | Div Expr Expr

eval :: Expr -> N Int
eval Var = do i <- get
              return i
eval (Con i) = return i
eval (Let e1 e2) = do v1 <- eval e1
                      put v1
                      v2 <- eval e2
                      return v2
eval (Add e1 e2) = do v1 <- eval e1
                      v2 <- eval e2
                      return (v1 + v2)
eval (Div e1 e2) = do v1 <- eval e1
                      v2 <- eval e2
                      if v2 == 0 then throw else return (v1 `div` v2)

eval' :: Expr -> (Maybe Int, Int)
eval' e = runSt (runMk (eval e)) 0
