--------------------------------------------------------------
data ES a = Var a | Read (Char -> ES a) | Write Char (ES a)

instance Show a => Show (ES a) where
  show (Var x) = show x
  show (Read _) = "Read"
  show (Write c e) = [c] ++ show e

-- bind
(>>==) :: ES a -> (a -> ES b) -> ES b
(Var x) >>== f = f x
(Read f) >>== g = Read (\c -> (f c) >>== g)
(Write c e) >>== f = Write c (e >>== f)

-- secuencia
(>>>) :: ES a -> ES b -> ES b
e1 >>> e2 = e1 >>== (\_ -> e2)

writeChar :: Char -> ES ()
writeChar c = Write c (Var ())

readChar :: ES Char
readChar = Read (\c -> Var c)

writeString :: String -> ES ()
writeString [] = Var ()
writeString (c:cs) = writeChar c >>> writeString cs

-- 9)

mapM' :: Monad m => (a -> m b) -> [a] -> m [b]
mapM' f [] = return []
mapM' f (l:ls) = do x <- f l
                    xs <- mapM' f ls
                    return (x:xs)

foldM' :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
foldM' f e [] = return e
foldM' f e (l:ls) = do x <- f e l
                       xs <- foldM' f x ls
                       return xs

-- 10)
f m h f g =
    do
        y <- do x <- m
                return (h x)
        z <- f y
        return (g z)

-- 11)
g = (y >>= \z -> f z >>= \w -> g w z) >>=
    h x 3 >>= \y -> if y 
                    then return 7
                    else h x 2 >>= \z -> return k z

-- 12)
-- NO SE SI ESTA BIEN
instance Monad a where
    (do return x
        f x) = f x
    (do t
        return) = t
    do (do t
           f)
        g    = do x <- t
                  f x
                  g


