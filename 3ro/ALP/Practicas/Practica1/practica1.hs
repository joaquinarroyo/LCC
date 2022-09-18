import Parsing

-- 2) 3)
expr :: Parser Int
expr = do t <- term
          do char '+'
             e <- expr
             return (t+e)
             <|>
             do char '-'
                e <- expr
                return (t-e)
                <|> 
                return t

term :: Parser Int
term = do f <- factor
          do char '*'
             t <- term
             return (f*t)
             <|>
             do char '/'
                t <- term
                return (div f t)
                <|> 
                return f

factor :: Parser Int
factor = do char '('
            e <- expr
            char ')'
            return e
            <|> 
            int

evaluate :: String -> Int
evaluate s = fst (head (parse expr s))
        
-- 4
data Expr = Num Int | BinOp Op Expr Expr deriving Show
data Op = Add | Mul | Min | Div deriving Show

expr' :: Parser Expr
expr' = do t <- term'
           do char '+'
              e <- expr'
              return (BinOp Add t e)
              <|>
              do char '-'
                 e <- expr'
                 return (BinOp Min t e)
                 <|> 
                 return t

term' :: Parser Expr
term' = do f <- factor'
           do char '*'
              t <- term'
              return (BinOp Mul f t)
              <|>
              do char '/'
                 t <- term'
                 return (BinOp Div f t)
                 <|> 
                 return f

factor' :: Parser Expr
factor' = do char '('
             e <- expr'
             char ')'
             return e
             <|> 
             do char '-'
                n <- nat
                return (Num (-n))
                <|>
                do n <- nat
                   return (Num n)

evaluate' :: Expr -> Int
evaluate' (Num x) = x
evaluate' (BinOp op l r) = (getOp op) (evaluate' l) (evaluate' r)
    where
        getOp Add = (+)
        getOp Min = (-)
        getOp Div = div
        getOp Mul = (*)

eval :: String -> Int
eval s = evaluate' (fst (head (parse expr' s)))

-- 5
-- parsea listas con numeros y caracteres 
listParser :: Parser String
listParser = do char '['
                v <- digit
                     <|>
                     listChar
                vs <- many1 (do char ','
                                do digit
                                   <|>
                                   listChar)
                char ']'
                return (v:vs)

listChar :: Parser Char 
listChar =  do char '\''
               x <- alphanum
               char '\''
               return x
-- 6
data Basetype = DInt | DChar | DFloat | Fun Basetype Basetype deriving Show
type Hasktype = [Basetype]

dparse :: Parser Hasktype
dparse = do t <- dtype
            ts <- many (do symbol "->"
                           dtype)
            return (t:ts)

dtype :: Parser Basetype
dtype =  do string "Int"
            return DInt
         <|>
         do string "Char"
            return DChar
         <|>
         do string "Float"
            return DFloat

-- 7)
-- Gramatica
-- S -> F -> S | F
-- F -> Int | Char | Float

s :: Parser Basetype
s =   do l <- dtype
         do symbol "->"
            r <- s
            return (Fun l r)
            <|>
            return l               

-- 8) Transformado en carpeta
expr2 :: Parser Expr
expr2 =  do t <- term2
            e' <- expr2'
            return (e' t)
            

expr2' :: Parser (Expr -> Expr)
expr2' = do char '+'
            t <- term2
            e' <- expr2'
            return (e' . (\e -> (BinOp Add e t)))
         <|>
         do char '-'
            t <- term2
            e' <- expr2'
            return (e' . (\e -> (BinOp Min e t)))
         <|>
         return id

term2 :: Parser Expr
term2 =  do f <- factor'
            t' <- term2'
            return (t' f)

term2' :: Parser (Expr -> Expr)
term2' = do char '*'
            f <- factor'
            t' <- term2' 
            return (t' . (\t -> (BinOp Mul t f)))
         <|>
         do char '/'
            f <- factor'
            t' <- term2'
            return (t' . (\t -> (BinOp Div t f)))
         <|>
         return id

-- -- 9)
-- declaration → type specifier declarator ’;’
-- declarator → ’*’ declarator | direct declarator
-- direct_declarator -> beta direct_declarator'
-- beta -> ( '(' direct_declarator ')'  | identifier ) direct_declarator'
-- direct_declarator' -> e | '[' contstant_expression ']' direct_declarator
-- type_specifier → ’int’ | ’char’ | ’float’
-- constant_expression → number

data Ctype = Cons Type Cdec | Inv deriving Show
data Cdec = Pun Cdec | Arr Cdec Int | Tup Cdec | I Identifier deriving Show
data Type = INT | CHAR | FLOAT deriving Show
type Identifier = String
type ConstantExpresion = Int

declaration :: Parser Ctype
declaration =  do t <- typeSpecifier
                  d <- declarator
                  symbol ";"
                  return (Cons t d)

declarator :: Parser Cdec
declarator =   do symbol "*"
                  d <- declarator
                  return (Pun d)
               <|>
               directDeclarator

directDeclarator :: Parser Cdec
directDeclarator =   do d <- (do symbol "("
                                 dd <- directDeclarator
                                 symbol ")"
                                 return (Tup dd)
                                 <|>
                                 do i <- ident
                                    return (I i))
                        dd <- directDeclarator'
                        return (dd d)

directDeclarator' :: Parser (Cdec -> Cdec)
directDeclarator' =  do symbol "["
                        ce <- constantExpression
                        symbol "]"
                        dd' <- directDeclarator'
                        return (\x -> dd' (Arr x ce))
                     <|>
                     return id

typeSpecifier :: Parser Type
typeSpecifier =   do symbol "int"
                     return INT
                  <|>
                  do symbol "char"
                     return CHAR
                  <|>
                  do symbol "float"
                     return FLOAT

constantExpression :: Parser ConstantExpresion
constantExpression = int

parseC :: String -> Ctype
parseC s = case parse declaration s of
            [] -> Inv
            l -> fst (head l)

