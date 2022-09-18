import qualified Arr as A
import Par
import Seq

emptyA :: A.Arr a
emptyA = A.empty

singletonA :: a -> A.Arr a
singletonA x = A.fromList [x]

lengthA :: A.Arr a -> Int
lengthA = A.length

nthA :: A.Arr a -> Int -> a
nthA v n = v A.! n

tabulateA :: (Int -> a) -> Int -> A.Arr a
tabulateA = A.tabulate

mapA :: (a -> b) -> A.Arr a -> A.Arr b
mapA f v = let l = lengthA v 
            in tabulateA (\i -> f (nthA v i)) l

filterA :: (a -> Bool) -> A.Arr a -> A.Arr a
filterA p v = let l = lengthA v
              in joinA (tabulateA (\i -> if p (nthA v i) 
                                        then singletonA (nthA v i) 
                                        else emptyA) l)

appendA :: A.Arr a -> A.Arr a -> A.Arr a
appendA v1 v2 = let l1 = lengthA v1
                    l2 = lengthA v2
                in tabulateA (\i -> if i < l1 then nthA v1 i 
                                    else nthA v2 (i - l1)) (l1 + l2)

takeA :: A.Arr a -> Int -> A.Arr a
takeA v n = A.subArray 0 n v

dropA :: A.Arr a -> Int -> A.Arr a
dropA v n = A.subArray n (lengthA v - 1) v

showtA :: A.Arr a -> TreeView a (A.Arr a)
showtA v = let l = lengthA v
               (d, rest) = (l `div` 2) ||| (l `mod` 2)
               (l1, l2) = (takeA v d) ||| (dropA v (d+rest))
           in 
             case l of
               0 -> EMPTY
               1 -> ELT (nthA v 0)
               _ -> NODE l1 l2

showlA :: A.Arr a -> ListView a (A.Arr a)
showlA v = let l = lengthA v
               (l1, l2) = (nthA v 0) ||| (dropA v 1)
           in 
             case l of
               0 -> NIL
               1 -> CONS l1 emptyA
               _ -> CONS l1 l2

joinA :: A.Arr (A.Arr a) -> A.Arr a
joinA v = A.flatten v

reduceA :: (a -> a -> a) -> a -> A.Arr a -> a
reduceA f x v = let l = lengthA v
                in
                  case l of
                    0 -> x
                    1 -> f x (nthA v 0)
                    _ -> let vs = contractA f v
                          in reduceA f x vs
              
-- aux ----------------------------------------------------
contractA :: (a -> a -> a) -> A.Arr a -> A.Arr a
contractA f v = let l = lengthA v
                in
                  tabulateA (\i -> if i < div l 2
                                   then f (nthA v (2*i)) (nthA v ((2*i)+1))
                                   else nthA v (2*i)) ((div l 2)+(mod l 2))                  

expandA :: (a -> a -> a) -> A.Arr a -> A.Arr a -> A.Arr a
expandA f v1 v2 = let l1 = lengthA v1
                   in tabulateA (\i -> if even i
                                     then nthA v2 (div i 2)
                                     else f (nthA v2 (div i 2)) (nthA v1 (i-1))) l1
-----------------------------------------------------------

scanA :: (a -> a -> a) -> a -> A.Arr a -> (A.Arr a, a)
scanA f x v = let l = lengthA v
                in case l of
                0 -> (emptyA, x)
                1 -> (singletonA x, f x (nthA v 0))
                _ -> let 
                        vs = contractA f v
                        (v', t) = scanA f x vs
                        in (expandA f v v', t)

fromListA :: [a] -> A.Arr a
fromListA = A.fromList

instance Seq A.Arr where
  emptyS = emptyA
  singletonS = singletonA
  lengthS = lengthA
  nthS = nthA
  tabulateS = tabulateA
  mapS = mapA
  filterS = filterA
  appendS = appendA
  takeS = takeA
  dropS = dropA
  showtS = showtA
  showlS = showlA
  joinS = joinA
  reduceS = reduceA
  scanS = scanA
  fromList = fromListA