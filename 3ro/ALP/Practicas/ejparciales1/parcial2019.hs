import Parsing

{- 
t := t + t | m nv | suc t | conv m t
m := ar$ | us$
nv := 0 | suc nv

t := b t'
b := m nv | suc t | conv m t
t' := e | '+' t t'
m := ar$ | us$
nv := 0 | suc nv

-}

data NVal = Zero | SucN NVal deriving Show
data Mon = AR | US deriving Show
data Term = Sum Term Term | Val Mon NVal |
            Conv Mon Term | SucT Term deriving Show

nvalParser :: Parser NVal
nvalParser = do char '0'
                return Zero
             <|>
             do string "suc"
                char '('
                n <- nvalParser
                char ')'
                return (SucN n)

moneyParser :: Parser Mon
moneyParser = do string "ar$"
                 return AR
              <|>
              do string "us$"
                 return US

termParser :: Parser Term
termParser = do t1 <- beta
                t2 <- termParser'
                return (t2 t1)

beta :: Parser Term
beta = do m <- moneyParser
          space
          n <- nvalParser
          return (Val m n)
        <|>
        do string "suc"
           char '('
           t <- termParser
           char ')'
           return (SucT t)
        <|>
        do string "conv"
           space
           m <- moneyParser
           space
           char '('
           t <- termParser
           char ')'
           return (Conv m t)

termParser' :: Parser (Term -> Term)
termParser' = do char '+'
                 t1 <- termParser
                 t2 <- termParser'
                 return (t2 . (\x -> (Sum x t1)))
              <|>
              return id