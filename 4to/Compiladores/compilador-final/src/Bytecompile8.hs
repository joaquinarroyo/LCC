{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Bytecompile8
  ( showOps8, string2bc8, bc2string8, bcWrite8, bcRead8, bc8, bytecompile8, runBC8 )
  where

{- Module 8ByteCompile -}

import Lang
import MonadFD4
import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word8, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord8 )
import Data.Binary.Get ( getWord8, isEmpty )
import Data.Char
import Bytecompile ( Bytecode, Module, openModule, ValBytecode(..), Env, Stack, dropDrops )


newtype Bytecode8 = BC8 { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 8 bits -}
instance Binary Bytecode8 where
  put (BC8 bs) = mapM_ putWord8 bs
  get = go
    where
      go = do
        empty <- isEmpty
        if empty
          then return $ BC8 []
          else do
            x <- getWord8
            BC8 xs <- go
            return $ BC8 (x:xs)


pattern NULL     = 0
pattern RETURN   = 1
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern CJUMP    = 16
pattern TAILCALL = 17
-- | Nuevos patterns para Enteros
pattern SHORT    = 18 -- 8bytes
pattern INT      = 19 -- 16bytes
pattern LONG     = 20 -- 32bytes


-- función util para debugging: muestra el Bytecode de forma más legible.
showOps8 :: Bytecode -> [String]
showOps8 []         = []
showOps8 (SHORT:xs) =
  let (n, xs') = getNumber (SHORT:xs)
  in ("SHORT " ++ show n) : showOps8 xs'
showOps8 (INT:xs)   =
  let (n, xs') = getNumber (INT:xs)
  in ("INT " ++ show n) : showOps8 xs'
showOps8 (LONG:xs)  =
  let (n, xs') = getNumber (LONG:xs)
  in ("LONG " ++ show n) : showOps8 xs'
showOps8 (NULL:xs)        = "NULL" : showOps8 xs
showOps8 (RETURN:xs)      = "RETURN" : showOps8 xs
showOps8 (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps8 xs
showOps8 (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show n) : showOps8 xs'
  where (n, xs') = getNumber (i:xs)
showOps8 (CALL:xs)        = "CALL" : showOps8 xs
showOps8 (ADD:xs)         = "ADD" : showOps8 xs
showOps8 (SUB:xs)         = "SUB" : showOps8 xs
showOps8 (FIX:xs)         = "FIX" : showOps8 xs
showOps8 (STOP:xs)        = "STOP" : showOps8 xs
showOps8 (JUMP:i:xs)      = ("JUMP off=" ++ show n) : showOps8 xs'
  where (n, xs') = getNumber (i:xs)
showOps8 (SHIFT:xs)       = "SHIFT" : showOps8 xs
showOps8 (DROP:xs)        = "DROP" : showOps8 xs
showOps8 (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string8 msg)) : showOps8 rest
showOps8 (PRINTN:xs)      = "PRINTN" : showOps8 xs
showOps8 (ADD:xs)         = "ADD" : showOps8 xs
showOps8 (CJUMP:i:xs)     = ("CJUMP off=" ++ show n) : showOps8 xs'
  where (n, xs') = getNumber (i:xs)
showOps8 (TAILCALL:xs)    = "TAILCALL" : showOps8 xs
showOps8 (x:xs)           = show x : showOps8 xs

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-8 del caracter.
string2bc8 :: String -> Bytecode
string2bc8 = map ord

bc2string8 :: Bytecode -> String
bc2string8 = map chr

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite8 :: Bytecode -> FilePath -> IO ()
bcWrite8 bs filename = BS.writeFile filename (encode $ BC8 $ fromIntegral <$> bs)

---------------------------
-- Ejecución de bytecode --
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead8 :: FilePath -> IO Bytecode
bcRead8 filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

-- | Transforma un Term en Bytecode
bc8 :: MonadFD4 m => TTerm -> m Bytecode
bc8 term = case term of
  (V _ (Bound i))                 -> return [ACCESS, i]
  (V _ (Free n))                  -> failFD4 "bc: Free"
  (Const _ (CNat i))              -> return (number2Bytecode i)
  (Lam _ _ _ (Sc1 t))             -> do
    t' <- tc8 t
    let n = number2Bytecode (length t')
    return $ [FUNCTION] ++ n ++ t'
  (App _ t1 t2)                   -> do
    t1' <- bc8 t1
    t2' <- bc8 t2
    return $ t1' ++ t2' ++ [CALL]
  (Print _ s t)                   -> do
    t' <- bc8 t
    return $ t' ++ [PRINT] ++ string2bc8 s ++ [NULL, PRINTN]
  (BinaryOp _ op t1 t2)           -> do
    t1' <- bc8 t1
    t2' <- bc8 t2
    case op of
      Add -> return $ t1' ++ t2' ++ [ADD]
      Sub -> return $ t1' ++ t2' ++ [SUB]
  (Fix _ _ _ _ _ (Sc2 t))         -> do
    t' <- bc8 t
    let n = number2Bytecode (length t' + 1)
    return $ [FUNCTION] ++ n ++ t' ++ [RETURN, FIX]
  (IfZ _ t1 t2 t3)                -> do
    t1' <- bc8 t1
    t2' <- bc8 t2
    t3' <- bc8 t3
    let n2 = number2Bytecode (length t3')
        n1 = number2Bytecode (length t2' + length n2 + 1)
    return $ t1' ++ [CJUMP] ++ n1 ++ t2' ++ [JUMP] ++ n2 ++ t3'
  (Let _ n ty t1 (Sc1 t2))        -> do
    t1' <- bc8 t1
    t2' <- bc8 t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]

tc8 :: MonadFD4 m => TTerm -> m Bytecode
tc8 term = case term of
  (App _ t1 t2) -> do
    t1' <- bc8 t1
    t2' <- bc8 t2
    return $ t1' ++ t2' ++ [TAILCALL]
  (IfZ _ t1 t2 t3) -> do
    t1' <- bc8 t1
    t2' <- tc8 t2
    t3' <- tc8 t3
    let n2 = number2Bytecode (length t3')
        n1 = number2Bytecode (length t2' + length n2 + 1)
    return $ t1' ++ [CJUMP] ++ n1 ++ t2' ++ [JUMP] ++ n2 ++ t3'
  (Let _ n ty t1 (Sc1 t2)) -> do
    t1' <- bc8 t1
    t2' <- tc8 t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]
  _ -> do
    term' <- bc8 term
    return $ term' ++ [RETURN]

-- | Ejecuta un bytecode
runBC8 :: MonadFD4 m => Bytecode -> m ()
runBC8 b = runBC8' b [] []

runBC8' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC8' b env s = tick >> maxStack (length s) >> runBC8'' b env s

runBC8'' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC8'' (RETURN:_) _ (v:(RA e c):stack)        = runBC8' c e (v:stack)
runBC8'' (SHORT:xs) env stack                   =
  let (i, xs') = getNumber (SHORT:xs)
  in runBC8' xs' env (I i:stack)
runBC8'' (INT:xs) env stack                     =
  let (i, xs') = getNumber (INT:xs)
  in runBC8' xs' env (I i:stack)
runBC8'' (LONG:xs) env stack                    =
  let (i, xs') = getNumber (LONG:xs)
  in runBC8' xs' env (I i:stack)
runBC8'' (ACCESS:i:xs) env stack                = runBC8' xs env (env!!i:stack)
runBC8'' (FUNCTION:ty:xs) env stack             = addClousure 1 >> 
  let (i, xs') = getNumber (ty:xs)
      drop' = drop i xs'
      take' = take i xs'
  in runBC8' drop' env (Fun env take':stack)
runBC8'' (CALL:xs) env (v:(Fun ef cf):stack)    = addClousure 1 >> runBC8' cf (v:ef) (RA env xs:stack)
runBC8'' (ADD:xs) env ((I i1):(I i2):stack)     = runBC8' xs env (I (i1 + i2):stack)
runBC8'' (SUB:xs) env ((I i1):(I i2):stack)     = runBC8' xs env (I (max 0 (i2 - i1)):stack)
runBC8'' (FIX:xs) env ((Fun ef cf):stack)       = addClousure 2 >>
  let envFix = Fun envFix cf:env
  in runBC8' xs env (Fun envFix cf:stack)
runBC8'' (STOP:xs) env (v:stack)                = return ()
runBC8'' (JUMP:ty:xs) env stack                 =
  let (i, xs') = getNumber (ty:xs)
  in runBC8' (drop i xs') env stack
runBC8'' (SHIFT:xs) env (v:stack)               = runBC8' xs (v:env) stack
runBC8'' (DROP:xs) (v:env) stack                = runBC8' xs env stack
runBC8'' (PRINT:xs) env stack                   =
  let (msg, _:xs') = span (/=NULL) xs
      s = bc2string8 msg
  in do printFD4nobreak s
        runBC8' xs' env stack
runBC8'' (PRINTN:xs) env s@(I i:stack)          =
  do printFD4 (show i)
     runBC8' xs env s
runBC8'' (CJUMP:ty:xs) env ((I c):stack)        = do
  let (i, xs') = getNumber (ty:xs)
  case c of
    0 -> runBC8' xs' env stack
    _ -> runBC8' (drop i xs') env stack
runBC8'' (TAILCALL:xs) env (v:(Fun ef cf):stack) =
  runBC8' cf (v:ef) stack

-- caso de fallo
runBC8'' i env stack = do
  printFD4 $ show (showOps8 i)
  printFD4 $ show env
  printFD4 $ show stack
  failFD4 "runBC8'': non-exhaustive patterns"

-- | Bytecompile
bytecompile8 :: MonadFD4 m => Module -> m Bytecode
bytecompile8 m = do
  bytecode8 <- bc8 $ openModule m
  return $ dropDrops (bytecode8 ++ [STOP])

-- |
getNumber :: Bytecode -> (Int, Bytecode)
getNumber (SHORT:xs)            = (head xs, tail xs)
getNumber (INT:x1:x2:xs)        = (x1 + x2 * 256, xs)
getNumber (LONG:x1:x2:x3:x4:xs) = (x1 + x2 * 256 + x3 * 256^2 + x4 * 256^4, xs)

-- | SHORT 8bits
--   INT   16bits
--   LONG  32bits
number2Bytecode :: Int -> Bytecode
number2Bytecode n
  | n < 256   = [SHORT, fromIntegral n]
  | n < 256^2 = [INT, fromIntegral (n `mod` 256), fromIntegral (n `div` 256)]
  | n < 256^4 = [LONG, fromIntegral (n `mod` 256), fromIntegral (n `div` 256 `mod` 256), fromIntegral (n `div` 256^2 `mod` 256), fromIntegral (n `div` 256^3)]

