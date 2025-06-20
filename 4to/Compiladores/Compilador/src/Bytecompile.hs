{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

{-
  Module      : Bytecompile
  Description : Compila a bytecode. Ejecuta bytecode.
  Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2023.
  License     : GPL-3
  Maintainer  : mauro@fceia.unr.edu.ar
  Stability   : experimental

  Este módulo permite compilar módulos a la Macchina. También provee
  una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  ( Bytecode, runBC, bcWrite, bcRead, showBC, bc, showOps,
    bytecompile, Module, openModule, ValBytecode(..), Env, Stack,
    dropDrops )
 where

import Lang
import MonadFD4
import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )
import Data.List ( intercalate )
import Data.Char
import Subst

type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where
      go = do
        empty <- isEmpty
        if empty
          then return $ BC []
          else do
            x <- getWord32le
            BC xs <- go
            return $ BC (x:xs)

{- 
  Estos sinónimos de patrón nos permiten escribir y hacer
  pattern-matching sobre el nombre de la operación en lugar del código
  entero, por ejemplo:

  f (CALL : cs) = ...

  Notar que si hubieramos escrito algo como
    call = 5
  no podríamos hacer pattern-matching con `call`.

  En lo posible, usar estos códigos exactos para poder ejectutar un
  mismo bytecode compilado en distintas implementaciones de la máquina.
-}

pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
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
-- | Nuevos patterns para IFZ
pattern CJUMP    = 16
pattern TAILCALL = 17


-- función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- Ejecución de bytecode --
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

-- | Transforma un Term en Bytecode
bc :: MonadFD4 m => TTerm -> m Bytecode
bc term = case term of
  (V _ (Bound i))                 -> return [ACCESS, i]
  (V _ (Free n))                  -> failFD4 "bc: Free"
  (Const _ (CNat i))              -> return [CONST, i]
  (Lam _ _ _ (Sc1 t))             -> do
    t' <- tc t
    return $ [FUNCTION, length t'] ++ t'
  (App _ t1 t2)                   -> do
    t1' <- bc t1
    t2' <- bc t2
    return $ t1' ++ t2' ++ [CALL]
  (Print _ s t)                   -> do
    t' <- bc t
    return $ t' ++ [PRINT] ++ string2bc s ++ [NULL, PRINTN]
  (BinaryOp _ op t1 t2)           -> do
    t1' <- bc t1
    t2' <- bc t2
    case op of
      Add -> return $ t1' ++ t2' ++ [ADD]
      Sub -> return $ t1' ++ t2' ++ [SUB]
  (Fix _ _ _ _ _ (Sc2 t))         -> do
    t' <- bc t
    return $ [FUNCTION, length t' + 1] ++ t' ++ [RETURN, FIX]
  (IfZ _ t1 t2 t3)                -> do
    t1' <- bc t1
    t2' <- bc t2
    t3' <- bc t3
    return $ t1' ++ [CJUMP, length t2' + 2] ++ t2' ++ [JUMP, length t3'] ++ t3'
  (Let _ n ty t1 (Sc1 t2))        -> do
    t1' <- bc t1
    t2' <- bc t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]

tc :: MonadFD4 m => TTerm -> m Bytecode
tc term = case term of
  (App _ t1 t2) -> do
    t1' <- bc t1
    t2' <- bc t2
    return $ t1' ++ t2' ++ [TAILCALL]
  (IfZ _ t1 t2 t3) -> do
    t1' <- bc t1
    t2' <- tc t2
    t3' <- tc t3
    return $ t1' ++ [CJUMP, length t2' + 2] ++ t2' ++ [JUMP, length t3'] ++ t3'
  (Let _ n ty t1 (Sc1 t2)) -> do
    t1' <- bc t1
    t2' <- tc t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]
  _ -> do
    term' <- bc term
    return $ term' ++ [RETURN]

-- | Bytecode Vals
data ValBytecode =
    I Int
  | Fun Env Bytecode
  | RA Env Bytecode

instance Show ValBytecode where
  show (I i) = show i
  show (Fun e b) = "Clos" ++ show (showOps b)
  show (RA e b) = "RA" ++ show (showOps b)

type Env = [ValBytecode]
type Stack = [ValBytecode]

-- | Ejecuta un bytecode
runBC :: MonadFD4 m => Bytecode -> m ()
runBC b = runBC' b [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC' b env s = tick >> maxStack (length s) >> runBC'' b env s

runBC'' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
runBC'' (RETURN:_) _ (v:(RA e c):stack)         = runBC' c e (v:stack)
runBC'' (CONST:i:xs) env stack                  = runBC' xs env (I i:stack)
runBC'' (ACCESS:i:xs) env stack                 = runBC' xs env (env!!i:stack)
runBC'' (FUNCTION:i:xs) env stack               = addClousure 1 >>
  let drop' = drop i xs
      take' = take i xs
  in runBC' drop' env (Fun env take':stack)
runBC'' (CALL:xs) env (v:(Fun ef cf):stack)     = addClousure 1 >> runBC' cf (v:ef) (RA env xs:stack)
runBC'' (ADD:xs) env ((I i1):(I i2):stack)      = runBC' xs env (I (i1 + i2):stack)
runBC'' (SUB:xs) env ((I i1):(I i2):stack)      = runBC' xs env (I (max 0 (i2 - i1)):stack)
runBC'' (FIX:xs) env ((Fun ef cf):stack)        = addClousure 2 >>
  let envFix = Fun envFix cf:env
  in runBC' xs env (Fun envFix cf:stack)
runBC'' (STOP:xs) env (v:stack)                 = return ()
runBC'' (JUMP:i:xs) env stack                   = runBC' (drop i xs) env stack
runBC'' (SHIFT:xs) env (v:stack)                = runBC' xs (v:env) stack
runBC'' (DROP:xs) (v:env) stack                 = runBC' xs env stack
runBC'' (PRINT:xs) env stack                    =
  let (msg, _:xs') = span (/=NULL) xs
      s = bc2string msg
  in do printFD4nobreak s
        runBC' xs' env stack
runBC'' (PRINTN:xs) env s@(I i:stack)           =
  do printFD4 (show i)
     runBC' xs env s
runBC'' (CJUMP:i:xs) env ((I c):stack)          =
  case c of
    0 -> runBC' xs env stack
    _ -> runBC' (drop i xs) env stack
runBC'' (TAILCALL:xs) env (v:(Fun ef cf):stack) = runBC' cf (v:ef) stack

-- caso de fallo
runBC'' i env stack                             = do
  printFD4 $ show (showOps i)
  printFD4 $ show env
  printFD4 $ show stack
  failFD4 "runBC'': non-exhaustive patterns"

-- | Modulo
type Module = [Decl TTerm]

-- | Bytecompile
bytecompile :: MonadFD4 m => Module -> m Bytecode
bytecompile m = do
  bytecode <- bc $ openModule m
  return $ dropDrops (bytecode ++ [STOP])

-- | Traduce una lista de declaraciones en una unica expresion "let in"
openModule :: Module -> TTerm
openModule [Decl _ n _ t]      = global2free n t
openModule ((Decl i n ty t):xs) = Let (i, getTy t) n ty t (close n (global2free n (openModule xs)))

-- | Cambia las variables globales por variables libres
global2free :: Name -> TTerm -> TTerm
global2free name = varChangerGlobal (\v p n -> if n == name then V p (Free n) else V p (Global n))

-- | El nombre lo dice todo. No es lo mas eficiente pero funciona.
dropDrops :: Bytecode -> Bytecode
dropDrops = reverse . dropWhile (== DROP) . reverse
