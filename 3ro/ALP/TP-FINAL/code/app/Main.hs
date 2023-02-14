module Main
  ( main
  ) where

import Command.AST
  ( Command(DeleteProfile, Exit, Export, Help, LS, LoadProfile,
        NewProfile, SaveProfile, ShowProfiles)
  )
import Command.Eval (eval)
import Control.Monad.Except (lift)
import Data.List (sort)
import Export.Exporter (export)
import Extra.Pp (printError, printPrompt, showEnv, showTasks)
import Monad.Env
  ( Env(..)
  , cleanSearchResult
  , getActualFolder
  , getProfileName
  , getRootFolder
  , getSearchResult
  , initEnv
  )
import Parser.Parser (ParseResult(Failed, Ok), comm_parse)
import Profile.Profile as P
  ( deleteProfile
  , firstLoad
  , lastProfileName
  , loadProfile
  , newProfile
  , saveProfile
  , showProfiles
  )
import Structures.Folder (newdir, getOrderedTasks)
import System.Console.Haskeline
  ( InputT(..)
  , defaultSettings
  , getInputLine
  , outputStrLn
  , runInputT
  )

-- main
main :: IO ()
main = runInputT defaultSettings loop
  where
    loop = do
      outputStrLn initialMessage
      -- Buscamos el ultimo perfil utilizado
      pn <- lift $ lastProfileName
      case pn of
        "" -> firstLoad "default"
        _ -> firstLoad pn
    firstLoad pn = do
      folder <- lift $ P.firstLoad pn
      case folder of
        -- Si existe el perfil pn
        Just folder' -> interpreter $ initEnv folder' pn
        -- Si se borro el perfil pn
        _ -> do
          lift $ newProfile pn
          interpreter $ initEnv newFolder pn
    newFolder = newdir "root"

-- Interprete
interpreter :: Env -> InputT IO ()
interpreter env = do
  input <- getInputLine $ printPrompt env
  case input of
    Nothing -> interpreter env
    Just "" -> interpreter env
    Just x -> do
      comm <- parseIO comm_parse x
      case comm of
        Just c -> do 
          menv <- handleCommand env c
          case menv of
            Nothing -> handleExit env
            Just env' -> interpreter env'
        _ -> interpreter env

-- Maneja los comandos
handleCommand :: Env -> Command -> InputT IO (Maybe Env)
handleCommand env comm =
  case comm of
    Exit -> return Nothing
    ----------- Comandos que producen salida -----------
    Help -> outputStrLn commands >> just env
    LS -> do
      case showEnv env of
        "" -> just env
        s -> do
          outputStrLn s
          just env
    ----------- Comandos que utilizan archivos -----------
    NewProfile name -> do
      msg <- lift $ newProfile name
      outputStrLn msg
      just env
    DeleteProfile -> do
      (b, msg) <- lift $ deleteProfile pn
      outputStrLn msg
      if b
        then handleCommand env (LoadProfile "default")
        else just env
    SaveProfile -> do
      msg <- lift $ saveProfile pn (getRootFolder env)
      outputStrLn msg
      just env
    LoadProfile name ->
      if name /= pn
        then do
          (folder, msg) <- lift $ loadProfile name
          outputStrLn msg
          case folder of
            Just folder' -> do
              lift $ saveProfile pn (getRootFolder env)
              just $ initEnv folder' name
            _ -> just env
        else just env
    ShowProfiles -> do
      profiles <- lift $ showProfiles
      outputStrLn profiles
      just env
    Export ft -> do
      let tasks' = getOrderedTasks $ getActualFolder env
          folderName = show $ getActualFolder env
      msg <- lift $ export ft folderName tasks'
      outputStrLn msg
      just env
    ----------- Demas comandos -----------
    _ ->
      case eval comm env of
        Left e -> do
          outputStrLn $ printError e
          just env
        Right env' ->
          case getSearchResult env' of
            [] -> just env'
            ts -> do
              outputStrLn $ showTasks $ sort ts
              just $ cleanSearchResult env'
  where
    pn = getProfileName env
    just = return . Just

-- Maneja el comando Exit
handleExit :: Env -> InputT IO ()
handleExit env = do
  input <- getInputLine $ "Do you want to save " ++ pn ++ " profile? (y/n) "
  case input of
    Just i ->
      case i of
        "y" -> do
          lift $ saveProfile pn (getRootFolder env)
          bye
        "n" -> bye
        _ -> handleExit env
    _ -> handleExit env
  where
    bye = lift $ putStrLn "Bye!"
    pn = getProfileName env

-- Funcion robada de TPs de ALP
parseIO :: (String -> ParseResult a) -> String -> InputT IO (Maybe a)
parseIO p x =
  lift $
  case p x of
    Failed e -> do
      putStrLn e
      return Nothing
    Ok r -> return (Just r)

-- Mensaje inicial, Comandos
initialMessage, commands :: String
initialMessage =
  "Lenguaje de organización de tareas\n\
    \Escriba help para recibir ayuda"
commands =
  "Comandos disponibles: \n\
    \  ls: lista las tareas/carpetas de la carpeta actual\n\
    \  cd <ruta>: cambia la carpeta actual a la ruta recibida\n\
    \  newdir <nombre>: crea una carpeta con el nombre recibido\n\
    \  newtask (<nombre>, <descripcion>, <prioridad - opcional>, <fecha - opcional>): crea una tarea con los datos recibidos\n\
    \  editdir <nombre>: edita la carpeta con el nombre recibido\n\
    \  edittask <nombre> set <campo> <valor>: edita el campo de la tarea con el nombre recibido\n\
    \  deletedir <nombre>: borra la carpeta con el nombre recibido\n\
    \  deletetask <nombre>: borra la tarea con el nombre recibido\n\
    \  completetask <nombre>: completa la tarea con el nombre recibido\n\
    \  search [-r] <filter>: busca las tareas/carpetas que cumplan con el filtro recibido\n\
    \        para conocer la sintaxis del lenguaje de filtros, revise la documentación\n\
    \        -r indica que la busqueda se realiza recursivamente\n\
    \  export <fileType>: exporta las tareas de la carpeta actual a un archivo .fileType\n\
    \        para saber los tipos de archivos disponibles, revise la documentación\n\
    \  newprofile <nombre>: crea un nuevo perfil con el nombre recibido\n\
    \  deleteprofile: elimina el perfil actual\n\
    \  showprofiles: muestra los perfiles creados\n\
    \  load <nombre>: carga el perfil con el nombre recibido\n\
    \  save: guarda el perfil actual\n\
    \  exit: cierra el programa\n\
    \  help: muestra los comandos disponibles"
