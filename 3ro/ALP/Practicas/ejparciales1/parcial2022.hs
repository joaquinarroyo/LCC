import Parsing

data Exp = N Int | V String | Ass Strng Exp |
           NewV Strng Exp Exp | BinOp Op Exp Exp
data Op = Sum | Mul

parser :: Parser Exp
pasrer = do e1 <- beta
            e2 <- parser'
            return (e2 e1)

beta :: Parser [Int]
beta = do string "newvar"
          space
          x <- many1 letter
          space
          char '='
          space
          e1 <- parser
          space
          string "in"
          space
          e2 <- parser
          return (NewV x e1 e2)
       <|>
       do x <- many letter
          many space
          string ":="
          many space
          e <- parser
          return (Ass x e)
       <|>
       do i <- int
          return (N i)
       do v <- many1 letter
          return (V v)

parser' :: Parser Exp
parser' = do char '+'
             e1 <- parser
             e2 <- parser'
             return (e2 . (\x -> BinOp Sum x e1))
          <|>
          do char '*'
             e1 <- parser
             e2 <- parser'
             retunr (e2 . (\x -> BinOp Mul x e1))
          <|>
          return id