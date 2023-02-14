module Structures.Task
  ( Name
  , Description
  , Completed
  , Priority(..)
  , Date(..)
  , Task(..)
  , Field(..)
  , newTask
  , completeTask
  , findTask
  , deleteTask
  ) where

import Data.Time (LocalTime(..))
import GHC.Generics

-- Sinonimos de tipos
type Name = String
type Description = String
type Completed = Bool

data Priority = P Integer deriving (Eq, Generic)

instance Show Priority where
  show (P 0) = "No priority"
  show (P p) = show p

instance Ord Priority where
  compare (P 0) (P 0) = EQ
  compare (P 0) _ = GT
  compare _ (P 0) = LT
  compare (P p1) (P p2) = compare p1 p2

instance Read Priority where
  readsPrec _ s = [(P (read s), "")]

-- Tipo utilizado para las fechas
data Date
  = Error
  | Null
  | T LocalTime
  deriving (Eq, Generic)

instance Show Date where
  show (T t) = show t
  show Null = "No date"

instance Ord Date where
  compare Null Null = EQ
  compare Null _ = LT
  compare _ Null = GT
  compare (T t1) (T t2) = compare t1 t2

instance Read Date where
  readsPrec _ s = [(T (read s), "")]

-- Fields de las tareas
data Field
  = Name
  | Description
  | Completed
  | Date
  | Priority
  deriving (Eq)

-- Tareas
data Task =
  Task
    { tname :: Name
    , description :: Description
    , completed :: Completed
    , priority :: Priority
    , date :: Date
    }
  deriving (Eq, Generic)

instance Show Task where
  show (Task n d True p t) =
    n ++ " | " ++ d ++ " | " ++ show p ++ " | " ++ show t ++ " | " ++ "✓"
  show (Task n d False p t) =
    n ++ " | " ++ d ++ " | " ++ show p ++ " | " ++ show t ++ " | " ++ "x"

instance Ord Task where
  compare (Task _ _ _ p1 t1) (Task _ _ _ p2 t2) =
    if p1 == p2
      then compare t1 t2
      else compare p1 p2
--

-- Crea una nueva tarea con los datos recibidos
newTask :: Name -> Description -> Priority -> Date -> Task
newTask n d p t =
  Task {tname = n, description = d, completed = False, priority = p, date = t}

-- Completa la tarea recibida
completeTask :: Task -> Task
completeTask t = t {completed = True}

-- Busca una tarea a partir de su nombre
findTask :: Name -> [Task] -> Maybe Task
findTask n [] = Nothing
findTask n (t:ts) =
  if n == tname t
    then Just t
    else findTask n ts

-- Borra una tarea a partir de su nombre
deleteTask :: Name -> [Task] -> [Task]
deleteTask n [] = []
deleteTask n (t:ts) =
  if n == tname t
    then deleteTask n ts
    else t : deleteTask n ts
