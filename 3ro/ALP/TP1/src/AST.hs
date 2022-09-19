module AST where

-- Identificadores de Variable
type Variable = String

-- Expresiones, aritmeticas y booleanas
data Exp a where
  -- Expresiones enteras
  Const :: Int -> Exp Int
  Var :: Variable -> Exp Int
  UMinus :: Exp Int -> Exp Int
  Plus :: Exp Int -> Exp Int -> Exp Int
  Minus :: Exp Int -> Exp Int -> Exp Int
  Times :: Exp Int -> Exp Int -> Exp Int
  Div :: Exp Int -> Exp Int -> Exp Int
  ECond :: Exp Bool -> Exp Int -> Exp Int -> Exp Int

  -- Expresiones booleanas
  BTrue :: Exp Bool
  BFalse :: Exp Bool
  Lt :: Exp Int -> Exp Int -> Exp Bool
  Gt :: Exp Int -> Exp Int -> Exp Bool
  And :: Exp Bool -> Exp Bool -> Exp Bool
  Or :: Exp Bool -> Exp Bool -> Exp Bool
  Not :: Exp Bool -> Exp Bool
  Eq :: Exp Int -> Exp Int -> Exp Bool
  NEq :: Exp Int -> Exp Int -> Exp Bool

deriving instance Show (Exp a)
deriving instance Eq (Exp a)

-- Comandos (sentencias)
-- Observar que solo se permiten variables de un tipo (entero)
data Comm
  = Skip
  | Let Variable (Exp Int)
  | Seq Comm Comm
  | IfThenElse (Exp Bool) Comm Comm
  | While (Exp Bool) Comm
  deriving (Show, Eq)

pattern IfThen :: Exp Bool -> Comm -> Comm
pattern IfThen b c = IfThenElse b c Skip

data Error = DivByZero | UndefVar deriving (Eq, Show)
