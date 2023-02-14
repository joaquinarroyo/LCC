module Monad.State
  ( MonadState(..)
  , MonadError(..)
  , State(..)
  ) where

import Control.Monad (ap, liftM)
import Extra.Error
import Filter.AST
import Filter.Lib as L (checkFilter, search, searchRecursive)
import Monad.Env
import Structures.Folder as F
import Structures.Route as R
import Structures.Task

-- Estado
newtype State a = State { runState :: Env -> Either Error (a, Env) }

instance Functor State where
  fmap = liftM

instance Applicative State where
  pure = return
  (<*>) = ap

instance Monad State where
  return x = State (\f -> Right (x, f))
  m >>= g =
    State
      (\f ->
         case runState m f of
           Left e -> Left e
           Right (x, (f1, f2, r, pn, sr)) -> runState (g x) (f1, f2, r, pn, sr))

-- MonadState
class Monad m => MonadState m where
    -- Setea la folder actual
  setFolder :: Folder -> m ()
    -- Devuelve la ruta actual
  getRoute :: m Route
    -- Setea la ruta
  setRoute :: Route -> m ()
    -- Devuelve la ruta sin el ultimo directorio
  backRoute :: m ()
    -- Setea el resultado de la busqueda
  setSearchResult :: [Task] -> m ()
    -- Agrega una tarea al folder system
  addTask :: Name -> Description -> Priority -> Date -> m ()
    -- Agrega una carpeta al folder system
  addDir :: Name -> m ()
    -- Borra una tarea
  deleteTask :: Name -> m ()
    -- Borra un directorio
  deleteDir :: Name -> m ()
    -- Edita una tarea
  editTask :: (Read a, Show a) => Name -> Field -> a -> m ()
    -- Edita el nombre de un directorio
  editDir :: Name -> m ()
    -- Chequea si la tarea esta en la carpeta actual
  taskInFolder :: Name -> m Bool
    -- Chequea si la carpeta esta en la carpeta actual
  folderInFolder :: Name -> m Bool
    -- Chequea si hay una carpeta con el nombre recibido a mismo nivel que la carpeta actual
  folderInParent :: Name -> m Bool
    -- Busca una carpeta a partir de una ruta
  findFolder :: Route -> m (Maybe Folder)
    -- Busca la carpeta padre
  findBackFolder :: m (Maybe Folder)
    -- Busca las tareas que cumplan con el filtro en la carpeta actual
  search :: Filter -> m [Task]
    -- Busca las tareas que cumplan con el filtro recursivamente desde la carpeta actual
  searchR :: Filter -> m [Task]

instance MonadState State where
  setFolder f = State (\(_, p, r, pn, sr) -> Right ((), (f, p, r, pn, sr)))
  getRoute = State (\e@(_, _, r, _, _) -> Right (r, e))
  setRoute route =
    State (\(f, p, r, pn, sr) -> Right ((), (f, p, R.addRoute r route, pn, sr)))
  backRoute = State (\(f, p, r, pn, sr) -> Right ((), (f, p, R.backRoute r, pn, sr)))
  setSearchResult ts = State (\(f, p, r, pn, _) -> Right ((), (f, p, r, pn, ts)))
  addTask name desc prio time =
    State
      (\(f, p, r, pn, sr) ->
         if R.inRoot r
           then Left CannotCreateTaskInRootDir
           else Right ((), (F.addTask task f, F.addTaskToRoot task p r, r, pn, sr)))
    where
      task = newTask name desc prio time
  addDir name =
    State
      (\(f, p, r, pn, sr) ->
         Right ((), (F.addDir newfolder f, F.addDirToRoot newfolder p r, r, pn, sr)))
    where
      newfolder = newdir name
  deleteTask name =
    State
      (\(f, p, r, pn, sr) ->
         Right ((), (F.deleteTask name f, F.deleteTaskFromRoot name p r, r, pn, sr)))
  deleteDir name =
    State
      (\(f, p, r, pn, sr) ->
         Right ((), (F.deleteDir name f, F.deleteDirFromRoot name p r, r, pn, sr)))
  editTask name field value =
    State
      (\(f, p, r, pn, sr) ->
         Right
           ( (), (F.editTask name field value f
                  , F.editTaskFromRoot name field value p r
                  , r
                  , pn
                  , sr)))
  editDir name =
    State
      (\(f, p, r, pn, sr) ->
         if R.inRoot r
           then Left CannotEditRootDir
           else Right
                  ( () , (f {fname = name}
                          , F.editDirFromRoot name p r
                          , R.editRoute r name
                          , pn
                          , sr)))
  taskInFolder name =
    State (\e@(f, p, r, pn, sr) -> Right (F.taskInFolder name f, e))
  folderInFolder name =
    State (\e@(f, p, r, pn, sr) -> Right (F.folderInFolder name f, e))
  folderInParent name =
    State (\e@(f, p, r, pn, sr) -> Right (F.folderInParent name r f, e))
  findFolder route = State (\e@(f, p, r, pn, sr) -> Right (F.findFolder route f, e))
  findBackFolder =
    State
      (\e@(f, p, r, pn, sr) ->
         Right
           ( case F.findParentFolder p r of
               Nothing -> Nothing
               Just f' -> Just f'
           , e))
  search filter =
    State
      (\e@(f, p, r, pn, sr) ->
         case L.checkFilter filter of
           Left e -> Left e
           Right _ -> Right (L.search filter f, e))
  searchR filter =
    State
      (\e@(f, p, r, pn, sr ) ->
         case L.checkFilter filter of
           Left e -> Left e
           Right _ -> Right (L.searchRecursive filter f, e))

-- MonadError
class (Monad m) => MonadError m where
  throw :: Error -> m a

instance MonadError State where
  throw e = State (\f -> Left e)
