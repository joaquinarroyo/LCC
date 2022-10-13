import Parsing
{- 

nv := n | n, nv
l := [nv] | n : l | [] | l ++ l

l = b l'
b = [nv] | n : l | [] 
l' = ++ l l'
nv := n | n, nv

-}

nvParser :: Parser [Int]
nvParser = do n <- int
              char ','
              l <- nvParser
              return (n:l)
           <|>
           do n <- int
              return [n]

lParser :: Parser [Int]
lParser = do b <- beta
             l <- lParser'
             return (l b)

beta :: Parser [Int]
beta = do char '['
          n <- nvParser
          char ']'
          return n
       <|>
       do n <- int
          char ':'
          l <- lParser
          return (n:l)
       <|>
       do char '['
          char ']'
          return []

lParser' :: Parser ([Int] -> [Int])
lParser' = do space
              string "++"
              space
              l <- lParser
              l' <- lParser'
              return (l'. (\x -> x ++ l))
           <|>
           return id