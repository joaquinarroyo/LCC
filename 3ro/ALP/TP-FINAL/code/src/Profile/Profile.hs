module Profile.Profile
  ( ProfileName
  , firstLoad
  , newProfile
  , deleteProfile
  , saveProfile
  , loadProfile
  , lastProfileName
  , showProfiles
  ) where

import Control.Monad.Except (join)
import Data.Aeson
import Data.List (isInfixOf)
import Extra.Error
  ( Error(CannotDeleteDefaultProfile, ErrorLoadingProfile,
      ProfileAlreadyExists, ProfileDoesNotExists)
  )
import Extra.Pp 
import Structures.Folder (Folder, newdir)
import Structures.Task (Task, Date, Priority)
import System.Directory (doesFileExist, getDirectoryContents, removeFile)

-- Instancias para utilizar .json
instance ToJSON Folder where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON Date where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON Priority where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON Task where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Folder where
  parseJSON = genericParseJSON defaultOptions
instance FromJSON Date where
  parseJSON = genericParseJSON defaultOptions
instance FromJSON Priority where
  parseJSON = genericParseJSON defaultOptions
instance FromJSON Task where
  parseJSON = genericParseJSON defaultOptions

type ProfileName = String

-- Crea/Carga el perfil default
firstLoad :: ProfileName -> IO (Maybe Folder)
firstLoad pn = do
  b <- doesFileExist $ route pn
  if b
    then do
      file <- readFile $ route pn
      return $ decode $ read file
    else do
      writeFile (route pn) $ show (encode $ dir)
      return $ Just dir
  where
    dir = newdir "root"

-- Crea un nuevo perfil con el nombre recibido
newProfile :: ProfileName -> IO (Message)
newProfile pn = do
  b <- doesFileExist $ route pn
  if b
    then return $ printError ProfileAlreadyExists
    else do
      writeFile (route pn) $ show (encode $ newdir "root")
      return $ printMessage "Profile created successfully"

-- Guarda el perfil en un archivo <pn>.json
saveProfile :: ProfileName -> Folder -> IO (Message)
saveProfile pn f = do
  writeFile (route pn) $ show (encode f)
  return $ printMessage "Profile saved successfully"

-- Carga el perfil desde un archivo .json a partir del nombre recibido
loadProfile :: ProfileName -> IO (Maybe Folder, Message)
loadProfile pn = do
  b <- doesFileExist $ route pn
  if b
    then do
      writeFile lastProfile $ pn
      file <- readFile $ route pn
      case decode $ read file of
        Just f -> return (Just f, printMessage "Profile loaded successfully")
        _ -> do
          return (Nothing, printError ErrorLoadingProfile)
    else return (Nothing, printError ProfileDoesNotExists)

-- Borra el perfil a partir de su nombre
deleteProfile :: ProfileName -> IO (Bool, Message)
deleteProfile pn =
  if pn == "default"
    then do
      return (False, printError CannotDeleteDefaultProfile)
    else do
      removeFile $ route pn
      return (True, printMessage "Profile deleted successfully")

-- Devuelve el nombre del ultimo perfil cargado
lastProfileName :: IO String
lastProfileName = do
  b <- doesFileExist lastProfile
  if b
    then do
      c <- readFile lastProfile
      return $ c
    else do
      writeFile lastProfile $ "default"
      return "default"

-- Devuelve los nombres de los perfiles creados
showProfiles :: IO String
showProfiles = do
  c <- getDirectoryContents "profiles"
  return $ printProfiles $ profiles c
  where
    profiles c = join $ map (\s -> (take (length s - 5) s) ++ " ") $ filter (isInfixOf ".json") c

-- Last profile file name
lastProfile :: String
lastProfile = "profiles/lastprofile.txt"

-- Profiles route
route :: String -> String
route s = "profiles/" ++ s ++ ".json"
