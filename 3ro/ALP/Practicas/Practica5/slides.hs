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

f :: ES String
f = readChar >>== g
    where g '\n' = Var []
          g c = f >>== (\xs -> Var (c:xs))

instance Functor ES where
  fmap f (Var x) = Var (f x)
  fmap f (Read g) = Read (\c -> fmap f (g c))
  fmap f (Write c e) = Write c (fmap f e)

instance Applicative ES where
  pure = Var
  (Var f) <*> e = e >>== (\x -> Var (f x))
  (Read f) <*> e = Read (\c -> (f c) <*> e)
  (Write c e1) <*> e2 = Write c (e1 <*> e2)

-- instancia Monad ES
instance Monad ES where
  return = Var
  (>>=) = (>>==)

-- Ejemplo de uso
main :: IO ()
main = do
  putStrLn "Escribe una cadena de caracteres:"
  s <- getLine
  putStrLn "La cadena de caracteres es:"
  putStrLn (show (writeString s))

-- main2 :: ES ()
-- main2 = do
--   writeString "Escribe una cadena de caracteres:"
--   s <- f
--   writeString "La cadena de caracteres es:"
--   writeString s
