module AST where

-- Identificadores de Variable
type Variable = String

-- Expresiones, aritmeticas y booleanas
data Exp a where
  -- Int
  Const ::Int -> Exp Int
  Var ::Variable -> Exp Int
  UMinus ::Exp Int -> Exp Int
  Plus ::Exp Int -> Exp Int -> Exp Int
  Minus ::Exp Int -> Exp Int -> Exp Int
  Times ::Exp Int -> Exp Int -> Exp Int
  Div ::Exp Int -> Exp Int -> Exp Int
  -- Bool
  BTrue ::Exp Bool
  BFalse ::Exp Bool
  Lt ::Exp Int -> Exp Int -> Exp Bool
  Gt ::Exp Int -> Exp Int -> Exp Bool
  And ::Exp Bool -> Exp Bool -> Exp Bool
  Or ::Exp Bool -> Exp Bool -> Exp Bool
  Not ::Exp Bool -> Exp Bool
  Eq ::Exp Int -> Exp Int -> Exp Bool
  NEq ::Exp Int -> Exp Int -> Exp Bool
  EAssgn ::Variable -> Exp Int -> Exp Int
  ESeq ::Exp Int -> Exp Int -> Exp Int
  
deriving instance Eq (Exp a)

instance Show (Exp a) where
  show (Const x) = show x
  show (Var v) = v
  show (UMinus e) = "-" ++ show e
  show (Plus x y) = show x ++ " + " ++ show y
  show (Minus x y) = show x ++ " - " ++ show y
  show (Times x y) = show x ++ " * " ++ show y
  show (Div x y) = show x ++ " / " ++ show y
  show BTrue = "True"
  show BFalse = "False"
  show (Lt x y) = show x ++ " < " ++ show y
  show (Gt x y) = show x ++ " > " ++ show y
  show (Eq x y) = show x ++ " == " ++ show y
  show (NEq x y) = show x ++ " != " ++ show y
  show (And x y) = show x ++ " && " ++ show y
  show (Or x y) = show x ++ " || " ++ show y
  show (Not b) = "!" ++ show b

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

type Trace = String
