module Filter.Eval
  ( evalFilter
  ) where

import Data.List (isInfixOf)
import Filter.AST (Filter(..))
import Structures.Task (Field(..), Task(..))  

-- Evaluador de las expresiones de filtros sobre una tarea
-- Los posibles errores son purgados anteriormente, en checkFilter
evalFilter :: Task -> Filter -> Bool
evalFilter t (FieldEq Name s) = tname t == s
evalFilter t (FieldEq Description s) = description t == s
evalFilter t (FieldIlike Name s) = isInfixOf s $ tname t
evalFilter t (FieldIlike Description s) = isInfixOf s $ description t
evalFilter t (FieldEqB b) = completed t == b
evalFilter t (FieldEqP p) = priority t == p
evalFilter t (FieldEqT d) = date t == d
evalFilter t (FieldNEq Name s) = tname t /= s
evalFilter t (FieldNEq Description s) = description t /= s
evalFilter t (FieldNEqB b) = completed t /= b
evalFilter t (FieldNEqP p) = priority t /= p
evalFilter t (FieldNEqT d) = date t /= d
evalFilter t (FieldGtP p) = priority t < p
evalFilter t (FieldLtP p) = priority t > p
evalFilter t (FieldGteP p) = priority t <= p
evalFilter t (FieldLteP p) = priority t >= p
evalFilter t (FieldGtT d) = date t > d
evalFilter t (FieldLtT d) = date t < d
evalFilter t (FieldGteT d) = date t >= d
evalFilter t (FieldLteT d) = date t <= d
evalFilter t (And e1 e2) =
  let v1 = evalFilter t e1
      v2 = evalFilter t e2
   in v1 && v2
evalFilter t (Or e1 e2) =
  let v1 = evalFilter t e1
      v2 = evalFilter t e2
   in v1 || v2
evalFilter t (Not e) =
  let v = evalFilter t e
   in not v