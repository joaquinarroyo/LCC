module Structures.Folder
  ( Folder(..)
  , newdir
  , addTask
  , addTaskToRoot
  , addDir
  , addDirToRoot
  , deleteTask
  , deleteTaskFromRoot
  , deleteDir
  , deleteDirFromRoot
  , editTask
  , editTaskFromRoot
  , editDir
  , editDirFromRoot
  , taskInFolder
  , folderInFolder
  , folderInParent
  , findFolder
  , findParentFolder
  , getOrderedTasks
  ) where

import Data.List (sort)
import Data.Map
import Extra.Lib (cast)
import GHC.Generics
import Prelude as P hiding (lookup)
import Structures.Route (Route(..), backRoute)
import Structures.Task as T hiding (deleteTask)

-- Carpeta con nombre, subcarpetas, tareas y ruta a carpeta padre
data Folder =
  Folder
    { fname :: String
    , folders :: Map Name Folder
    , tasks :: Map Name Task
    }
  deriving (Eq, Generic)

instance Show Folder where
  show (Folder n fs ts) = n

instance Ord Folder where
  compare (Folder n _ _) (Folder n' _ _) = compare n n'

-- Crea una nueva carpeta con el nombre recibido y setea la carpeta padre
newdir :: Name -> Folder
newdir n = Folder {fname = n, folders = empty, tasks = empty}

-- Crea una nueva tarea con el nombre recibido sobre la carpeta recibida
addTask :: Task -> Folder -> Folder
addTask t f = f {tasks = insert (tname t) t (tasks f)}

-- Agrega una carpeta a la carpeta recibida
addDir :: Folder -> Folder -> Folder
addDir f' f = f {folders = insert (fname f') f' (folders f)}

-- Agrega una tarea en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
addTaskToRoot :: Task -> Folder -> Route -> Folder
addTaskToRoot t f Empty = f {tasks = insert (tname t) t (tasks f)}
addTaskToRoot t (Folder n fs ts) (Route n' r) =
  case lookup n' fs of
    Just f' -> Folder n (insert n' (addTaskToRoot t f' r) fs) ts
    Nothing -> Folder n fs ts

-- Agrega una carpeta en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
addDirToRoot :: Folder -> Folder -> Route -> Folder
addDirToRoot f f' Empty = f' {folders = insert (fname f) f (folders f')}
addDirToRoot f (Folder n fs ts) (Route n' r) =
  case lookup n' fs of
    Just f' -> Folder n (insert n' (addDirToRoot f f' r) fs) ts
    Nothing -> Folder n fs ts

-- Busca una tarea con nombre 'n' en la lista de tareas recibida
deleteTask :: Name -> Folder -> Folder
deleteTask n f = f {tasks = delete n (tasks f)}

-- Elimina una carpeta de la carpeta recibida
deleteDir :: Name -> Folder -> Folder
deleteDir n f = f {folders = delete n (folders f)}

-- Elimina una tarea con nombre 'n' en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
deleteTaskFromRoot :: Name -> Folder -> Route -> Folder
deleteTaskFromRoot n f Empty = f {tasks = delete n (tasks f)}
deleteTaskFromRoot n (Folder n' fs ts) (Route n'' r) =
  case lookup n'' fs of
    Just f' -> Folder n' (insert n'' (deleteTaskFromRoot n f' r) fs) ts
    Nothing -> Folder n' fs ts

-- Elimina una carpeta en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
deleteDirFromRoot :: Name -> Folder -> Route -> Folder
deleteDirFromRoot n f Empty = f {folders = delete n (folders f)}
deleteDirFromRoot n (Folder n' fs ts) (Route n'' r) =
  case lookup n'' fs of
    Just f' -> Folder n' (insert n'' (deleteDirFromRoot n f' r) fs) ts
    Nothing -> Folder n' fs ts

-- Edita una tarea con nombre 'n' de la carpeta recibida
editTask :: Show a => Name -> Field -> a -> Folder -> Folder
editTask n Name s fl@(Folder n' fs ts) =
  case lookup n ts of
    Just t' -> fl {tasks = insert s' (t' {tname = s'}) ts'}
    Nothing -> fl
  where
    ts' = delete n ts
    s' = cast s :: String
editTask n f s fl@(Folder n' fs ts) = 
  case lookup n ts of
    Just t' -> 
      case f of
        Description -> fl {tasks = insert n (t' {description = cast s :: String}) ts}
        Date -> fl {tasks = insert n (t' {date = cast s :: Date}) ts}
        Completed -> fl {tasks = insert n (t' {completed = cast s :: Bool}) ts}
        Priority -> fl {tasks = insert n (t' {priority = cast s :: Priority}) ts}
    _ -> fl
      
-- Edita una tarea con nombre 'n' en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
editTaskFromRoot :: Show a => Name -> Field -> a -> Folder -> Route -> Folder
editTaskFromRoot n f s f' Empty = editTask n f s f'
editTaskFromRoot n f s (Folder n' fs ts) (Route n'' r) =
  case lookup n'' fs of
    Just f'' -> Folder n' (insert n'' (editTaskFromRoot n f s f'' r) fs) ts
    Nothing -> Folder n' fs ts

-- Edita el nombre de la carpeta recibida
editDir :: Name -> Folder -> Folder
editDir n f = f {fname = n}

-- Edita el nombre de la carpeta en la ruta recibida
-- Es necesario para mantener actualizado el directorio root
editDirFromRoot :: Name -> Folder -> Route -> Folder
editDirFromRoot n (Folder n' fs ts) (Route n'' Empty) =
  case lookup n'' fs of
    Just f' -> Folder n' (insert n (editDir n f') fs') ts
    Nothing -> Folder n' fs ts
  where
    fs' = delete n'' fs
editDirFromRoot n (Folder n' fs ts) (Route n'' r) =
  case lookup n'' fs of
    Just f' -> Folder n' (insert n'' (editDirFromRoot n f' r) fs) ts
    Nothing -> Folder n' fs ts

-- Chequea si existe una tarea con nombre 'n' en la carpeta recibida
taskInFolder :: Name -> Folder -> Bool
taskInFolder n (Folder _ _ ts) = lookupInFolder n ts

-- Chequea si existe una carpeta con nombre 'n' en la carpeta recibida
folderInFolder :: Name -> Folder -> Bool
folderInFolder n (Folder _ fs _) = lookupInFolder n fs

-- Funcion auxiliar para buscar en mapa
lookupInFolder :: Name -> Map Name a -> Bool
lookupInFolder n m =
  case lookup n m of
    Just _ -> True
    _ -> False

-- Chequea si existe una carpeta con nombre 'n' en la carpeta recibida o en alguna de sus subcarpetas
folderInParent :: Name -> Route -> Folder -> Bool
folderInParent n Empty f = folderInFolder n f
folderInParent n (Route n' r) f =
  case lookup n' (folders f) of
    Just f' -> folderInParent n r f'
    Nothing -> False

-- Busca una tarea con nombre 'n' en la carpeta recibida
findFolder :: Route -> Folder -> Maybe Folder
findFolder Empty f = Just f
findFolder (Route n r) f =
  case lookup n (folders f) of
    Just f' -> findFolder r f'
    Nothing -> Nothing

-- Busca una tarea con nombre 'n' a partir de la ruta recibida, desde el directorio root
findParentFolder :: Folder -> Route -> Maybe Folder
findParentFolder f r = findFolder route f
  where
    route = backRoute r

-- Devuelve las tareas ordenadas
getOrderedTasks :: Folder -> [Task]
getOrderedTasks f = sort $ P.map snd $ toList $ tasks f
