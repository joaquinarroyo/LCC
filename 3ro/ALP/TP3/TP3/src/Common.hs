module Common where

  -- Comandos interactivos o de archivos
  data Stmt i = Def String i           --  Declarar un nuevo identificador x, let x = t
              | Eval i                 --  Evaluar el término
    deriving (Show)
  
  instance Functor Stmt where
    fmap f (Def s i) = Def s (f i)
    fmap f (Eval i)  = Eval (f i)

  -- Tipos de los nombres
  data Name
     =  Global  String
    deriving (Show, Eq)

  -- Entornos
  type NameEnv v t = [(Name, (v, t))]

  -- Tipo de los tipos
  data Type = EmptyT 
            | FunT Type Type
            -- Sección 8
            | UnitT
            -- Sección 9
            | PairT Type Type
            -- Sección 10
            | NatT
            deriving (Show, Eq)
  
  -- Términos con nombres
  data LamTerm  =  LVar String
                |  LAbs String Type LamTerm
                |  LApp LamTerm LamTerm
                -- Sección 6
                |  LLet String LamTerm LamTerm
                -- Sección 7
                |  LAs LamTerm Type
                -- Sección 8
                |  LUnit
                -- Sección 9
                |  LFst LamTerm
                |  LSnd LamTerm
                |  LPair LamTerm LamTerm
                -- Sección 10
                |  LZero
                |  LSuc LamTerm
                |  LRec LamTerm LamTerm LamTerm
                deriving (Show, Eq)


  -- Términos localmente sin nombres
  data Term  = Bound Int
             | Free Name 
             | Term :@: Term
             | Lam Type Term
             -- Sección 6
             | Let Term Term
             -- Sección 7
             | As Term Type
             -- Sección 8
             | Unit
             -- Sección 9
             | Fst Term
             | Snd Term
             | Pair Term Term
             -- Sección 10
             | Zero
             | Suc Term
             | Rec Term Term Term
          deriving (Show, Eq)

  -- Valores
  data Value = VLam Type Term 
             -- Sección 8
             | VUnit
             -- Sección 9
             | VPair Value Value
             -- Sección 10
             | VNum NumVal
           deriving (Show, Eq)

  -- Valores Numericos, Sección 10
  data NumVal = NZero | NSuc NumVal deriving (Show, Eq)

  -- Contextos del tipado
  type Context = [Type]
