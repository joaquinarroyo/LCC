module Structures.Route
  ( Route(..)
  , addRoute
  , backRoute
  , editRoute
  , inRoot
  ) where

import Structures.Task (Name)

-- Ruta de directorios
data Route
  = Empty
  | Back
  | Route Name Route
  deriving (Eq)

instance Show Route where
  show Empty = ""
  show Back = "Back"
  show (Route n r) = n ++ "/" ++ show r

--
-- Appendea dos rutas
addRoute :: Route -> Route -> Route
addRoute Empty r2 = r2
addRoute (Route n r1) r2 = Route n (addRoute r1 r2)

-- Quita el ultimo directorio de la ruta
backRoute :: Route -> Route
backRoute Empty = Empty
backRoute (Route n Empty) = Empty
backRoute (Route n (Route _ Empty)) = Route n Empty
backRoute (Route n r) = Route n (backRoute r)

-- Edita el nombre del ultimo directorio de la ruta
editRoute :: Route -> Name -> Route
editRoute Empty _ = Empty
editRoute (Route n Empty) n' = Route n' Empty
editRoute (Route n r) n' = Route n (editRoute r n')

-- Chequea si la ruta esta en root o no
inRoot :: Route -> Bool
inRoot Empty = True
inRoot _ = False
