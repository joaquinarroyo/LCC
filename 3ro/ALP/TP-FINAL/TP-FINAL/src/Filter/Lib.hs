module Filter.Lib
  ( checkFilter
  , search
  , searchRecursive
  ) where

import Data.Map
import Extra.Error
import Filter.AST
import Filter.Eval
import Structures.Folder
import Structures.Task

-- Chequea que el filtro sea correcto
-- Nos permite agregar mas chequeos sobre los filtros
-- Chequea: Fecha
checkFilter :: Filter -> Either Error Filter
checkFilter f@(FieldEqT d) = checkDate f d
checkFilter f@(FieldNEqT d) = checkDate f d
checkFilter f@(FieldGtT d) = checkDate f d
checkFilter f@(FieldLtT d) = checkDate f d
checkFilter f@(FieldGteT d) = checkDate f d
checkFilter f@(FieldLteT d) = checkDate f d
checkFilter (And e1 e2) = do
  f1 <- checkFilter e1
  f2 <- checkFilter e2
  return $ And f1 f2
checkFilter (Or e1 e2) = do
  f1 <- checkFilter e1
  f2 <- checkFilter e2
  return $ Or f1 f2
checkFilter (Not e) = checkFilter e
checkFilter f = Right f

-- Chequea que la fecha sea correcta
checkDate :: Filter -> Date -> Either Error Filter
checkDate _ Error = Left WrongDateFormat
checkDate f d = Right f

-- Busca tareas que cumplan con el filtro recibido en la carpeta recibida
search :: Filter -> Folder -> [Task]
search f (Folder _ _ ts) = search' f (toList ts)

search' :: Filter -> [(Name, Task)] -> [Task]
search' f [] = []
search' f ((_, t):ts) =
  if evalFilter t f
    then t : search' f ts
    else search' f ts

-- Busca tareas que cumplan con el filtro recibido en la carpeta recibida, recursivamente
searchRecursive :: Filter -> Folder -> [Task]
searchRecursive f (Folder _ fs ts) =
  searchRecursive' f (toList ts) ++ concatMap (searchRecursive f) (elems fs)

searchRecursive' :: Filter -> [(Name, Task)] -> [Task]
searchRecursive' f [] = []
searchRecursive' f ((_, t):ts) =
  if evalFilter t f
    then t : searchRecursive' f ts
    else searchRecursive' f ts
