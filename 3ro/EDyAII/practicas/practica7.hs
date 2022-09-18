import ListSeq
import Par

-- 1)
-- a)

promedios :: [Int] -> [Int]
promedios l = let 
                   (sumas, max) = scanL (+) 0 l
                   sumas' = dropL sumas 1
                   largo = lengthL l
               in
                   tabulateL (\i -> div (nthL sumas' i) (i+1)) largo

-- b)

aux :: [Int] -> Int -> Bool
aux [] _ = True
aux (x:xs) y = y > x && (aux xs y)

getLastNumber :: [Int] -> Int
getLastNumber l = nthL l i
        where 
            i = (lengthL l) - 1 

mayores :: [Int] -> Int
mayores l = let
                (ll, lr) = scanL max 0 l
                lista = appendL (dropL ll 1) (singletonL lr)
            in
                reduceL (+) 0 (tabulateL 
                                (\i -> if (nthL lista i) < (nthL l (i+1))
                                then 1 else 0) ((lengthL lista) - 1))

-- 2)
multiMatr :: (Int, Int, Int, Int) -> (Int, Int, Int, Int) -> (Int, Int, Int, Int)
multiMatr (a, b, c ,d) (w, x, y, z) = (a*w + b*y, a*x + b*z, c*w + d*y, c*x + d*z) 
 
fibSeq :: Int -> [Int]
fibSeq n = let
            (l, last) = scanL multiMatr (1, 0, 0, 0) (tabulateL (\i -> (1,1,1,0)) n)
            l' = appendL l (singletonL last)
            in
                tabulateL (\i -> (\(a, b, c, d) -> b) (nthL l' i)) (lengthL l')
        

-- 3)
maxL :: [Int] -> Int
maxL xs = reduceL max 0 xs

aguaHist :: [Int] -> Int
aguaHist l = let 
                lista = tabulateL (\i -> max 0 ((min (maxL (takeL l i)) 
                        (maxL (dropL l (i+1))) - (nthL l i)))) ((lengthL l) - 1)
             in
                reduceL (+) 0 lista

-- 4)
data Paren = Neutro | Open | Close deriving (Show, Eq)
l = [Open, Open, Open, Close, Close, Close]


matchParen :: [Paren] -> Bool
matchParen l = let
                l' = mapL singletonL l
                (prefijos, final) = scanL (++) [] l'
                lista = appendL (drop 1 prefijos) (singletonL final) -- tenemos todas las subsecuencias
                (cont, conts) = 
                    reduceL (+) 0 (tabulateL (\i -> if nthL l i == Open
                                                    then 1 else -1) (lengthL l))
                        |||
                    tabulateL (\i -> (reduceL (+) 0 (tabulateL (\j -> if nthL (nthL lista i) j == Open
                                            then 1 else -1) (lengthL (nthL lista i))))
                                            ) (lengthL lista)
                in 
                    cont == 0 && (reduceL (+) 0 conts >= 0)

matchP :: [Paren] -> (Int, Int)
matchP l = case showtL l of
                EMPTY -> (0, 0)
                (ELT e) -> case e of
                    Open -> (1, -1)
                    Close -> (-1, 1)
                (NODE l r) -> let
                                (a, b) = matchP l
                                (c, d) = matchP r
                                in
                                    (a + c, b + d)        

matchParenV2 :: [Paren] -> Bool
matchParenV2 l = matchP l == (0, 0)

-- 5)
aux1 :: Int -> Int -> Int
aux1 n 0 = n
aux1 n m = n+m

sccml :: [Int] -> [[Int]]
sccml l = tabulateL (\i -> (tabulateL (\j -> if nthL (nthL l i) j < nthL (nthL l i) (j+1)
                                            then 1 else 0) ((lengthL (nthL l i))-1))) (lengthL l)
                -- reduceL (+) 0 counts

-- 6)

multiplos :: [Int] -> Int
multiplos l = let 
                l' = joinL (tabulateL (\i -> mapL (mod (nthL l i)) (dropL l (i+1))) ((lengthL l) - 1))
                l'' = tabulateL (\i -> if nthL l' i == 0 
                                    then 1 else 0) (lengthL l')
              in
                  reduceL (+) 0 l''


                 

