import Control.Monad (liftM, ap)
import Control.Applicative (Applicative(..))
import Data.Char

newtype MEstado m s a = Es {runSt :: s -> m (a, s)}

instance Monad m => Functor (MEstado m s) where
    fmap = liftM

instance Monad m => Applicative (MEstado m s) where
    pure  = return
    (<*>) = ap

instance Monad m => Monad (MEstado m s) where
    return x = Es (\s -> return (x, s))
    (Es h) >>= f = Es (\s -> do (x, s') <- h s
                                runSt (f x) s')

type Parser a = MEstado [] String a

falla :: Parser a
falla = Es (\s -> [])

item :: Parser Char
item = Es (\s -> case s of
                   [] -> []
                   (x:xs) -> [(x, xs)])

(+++) :: Parser a -> Parser a -> Parser a
p1 +++ p2 = Es (\s -> case runSt p1 s of
                        [] -> runSt p2 s
                        r -> r)

cadena :: String -> Parser String
cadena [] = Es (\s -> return ("", s))
cadena (x:xs) = do c <- item
                   if c == x
                   then do cs <- cadena xs
                           return (c:cs)
                   else falla

data Base = Int | Char | Bool
data Type = L Base | Fun Base Type | Base Base

instance Show Base where
    show Int = "Int"
    show Char = "Char"
    show Bool = "Bool"

instance Show Type where
    show (L b) = "[" ++ show b ++ "]"
    show (Fun b t) = show b ++ " -> " ++ show t
    show (Base b) = show b

parserTy :: Parser Type
parserTy = do (do cadena "["
                  t <- parserBase
                  cadena "]"
                  return (L t))
               +++
               (do t1 <- parserBase
                   cadena "->"
                   t2 <- parserTy
                   return (Fun t1 t2))
               +++
               (do t <- parserBase
                   return (Base t))

parserBase :: Parser Base
parserBase = do (do cadena "int"
                    return Int)
                +++
                (do cadena "char"
                    return Char)
                +++
                (do cadena "bool"
                    return Bool)

parse :: Parser a -> String -> [(a, String)]
parse p s = runSt p s
