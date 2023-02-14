module Monad.Env
  ( Env
  , initEnv
  , getActualFolder
  , getRootFolder
  , getRoute
  , getProfileName
  , getSearchResult
  , cleanSearchResult
  ) where

import Structures.Folder (Folder(..))
import Structures.Route (Route(..))
import Structures.Task (Task(..))

-- (actual folder, root folder, actual route, profile name, search result)
type Env = (Folder, Folder, Route, String, [Task])

-- Inicializa el ambiente
initEnv :: Folder -> String -> Env
initEnv f pn = (f, f, Empty, pn, [])

-- Devuelve la carpeta actual
getActualFolder :: Env -> Folder
getActualFolder (f, _, _, _, _) = f

-- Devuelve la carpeta root
getRootFolder :: Env -> Folder
getRootFolder (_, f, _, _, _) = f

-- Devuelve la ruta
getRoute :: Env -> Route
getRoute (_, _, r, _, _) = r

-- Devuelve el nombre del perfil
getProfileName :: Env -> String
getProfileName (_, _, _, pn, _) = pn

-- Devuelve el resultado de la busqueda
getSearchResult :: Env -> [Task]
getSearchResult (_, _, _, _, ts) = ts

-- Resetea el search result
cleanSearchResult :: Env -> Env
cleanSearchResult (f, rf, r, pn, _) = (f, rf, r, pn, [])

