module Command.Eval
  ( eval
  ) where

import Command.AST (Command(..))
import Extra.Error (Error(..))
import Monad.Env (Env)
import Monad.State (MonadError(..), MonadState(..), State(runState))
import Structures.Route (Route(..))
import Structures.Task (Date(..), Field(..), Name)

-- Evaluador de comandos
eval :: Command -> Env -> Either Error Env
eval comm env =
  case runState (eval' comm) env of
    Left e -> Left e
    Right (_, env') -> Right env'

-- Funcion auxiliar para eval
eval' :: (MonadState m, MonadError m) => Command -> m ()
eval' (NewTask n d p t) = do
  b <- taskInFolder n
  if b
    then throw TaskAlreadyExists
    else case t of
           Error -> throw WrongDateFormat
           _ -> do
             addTask n d p t
eval' (DeleteTask s) = do
  deleteTask s
eval' (EditTaskName n s) = do
  b <- taskInFolder n
  if not b
    then throw TaskNotFound
    else do
      b' <- taskInFolder s
      if b'
        then throw TaskAlreadyExists
        else do
          editTask n Name s
eval' (EditTaskDate n t) = do
  b <- taskInFolder n
  if not b
    then throw TaskNotFound
    else case t of
           Error -> throw WrongDateFormat
           _ -> do
             editTask n Date t
eval' (EditTaskDescription n s) = editTaskAux n Description s
eval' (EditTaskPriority n p) = editTaskAux n Priority p
eval' (EditTaskCompleted n b) = editTaskAux n Completed b
eval' (NewDir s) = do
  b <- folderInFolder s
  if b
    then throw DirAlreadyExists
    else do
      addDir s
eval' (DeleteDir s) = do
  deleteDir s
eval' (EditDir s) = do
  b <- folderInParent s
  if b
    then throw DirAlreadyExists
    else do
      editDir s
eval' (CD Back) = do
  f <- findBackFolder
  case f of
    Just f' -> do
      setFolder f'
      backRoute
    _ -> return ()
eval' (CD r) = do
  f <- findFolder r
  case f of
    Nothing -> throw DirNotFound
    Just f' -> do
      setFolder f'
      setRoute r
eval' (Search f False) = do
  l <- search f
  setSearchResult l
eval' (Search f True) = do
  l <- searchR f
  setSearchResult l

-- Funcion auxiliar para editar tareas
editTaskAux :: (MonadState m, MonadError m, Read a, Show a) => Name -> Field -> a -> m ()
editTaskAux n f a = do
  b <- taskInFolder n
  if not b
    then throw TaskNotFound
    else do
      editTask n f a
