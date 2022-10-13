import Parsing

{- 
e := n | e + e | head se
se := always e | cons (e,se) | tail se | ifz (e,se,se)

e := b e'
b := n | head se
e' := + e e'
se := always e | cons (e,se) | tail se | ifz (e,se,se)

-}

data ExpInt = Sum ExpInt ExpInt | Head ExpSt | E Int deriving Show
data ExpSt = Always ExpInt | Cons ExpInt ExpSt | Tail ExpSt | IFZ ExpInt ExpSt ExpSt deriving Show

eParser :: Parser ExpInt
eParser = do t1 <- beta
             t2 <- eParser'
             return (t2 t1)

beta :: Parser ExpInt
beta = do i <- int
          return (E i)
       <|>
       do string "head"
          space
          char '('
          se <- seParser
          char ')'
          return (Head se)

eParser' :: Parser (ExpInt -> ExpInt)
eParser' = do char '+'
              e1 <- eParser
              e2 <- eParser'
              return (e2 . (\x -> Sum x e1))
           <|>
           return id

seParser :: Parser ExpSt
seParser = do string "always"
              space
              char '('
              e <- eParser
              char ')'
              return (Always e)
           <|>
           do string "cons"
              space
              char '('
              e <- eParser
              char ','
              se <- seParser
              char ')'
              return (Cons e se)
           <|>
           do string "tail"
              space
              char '('
              se <- seParser
              char ')'
              return (Tail se)
           <|>
           do string "ifz"
              space
              char '('
              e <- eParser
              char ','
              se1 <- seParser
              char ','
              se2 <- seParser
              char ')'
              return (IFZ e se1 se2)