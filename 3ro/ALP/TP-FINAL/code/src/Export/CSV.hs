module Export.CSV
  ( export
  ) where

import qualified Data.ByteString.Lazy as BL
import Data.Csv
import Data.Time (LocalTime(..))
import Structures.Task

-- Instancias para poder exportar a CSV
instance ToField Completed where
  toField True = toField "Completed"
  toField False = toField "Not completed"

instance ToField LocalTime where
  toField t = toField $ show t

instance ToField Date where
  toField (T t) = toField t
  toField Null = toField "No date"
  toField Error = toField "Error"

instance ToField Priority where
  toField (P 0) = toField "No priority"
  toField (P p) = toField p

instance ToRecord Char where
  toRecord c = record [toField c]

instance ToRecord Task where
  toRecord (Task n d c p dt) =
    record [toField n, toField d, toField c, toField p, toField dt]

--
-- Funcion que exporta las tareas a un archivo CSV
export :: String -> [Task] -> IO ()
export folderName tasks = do
  BL.writeFile filePath . encode $ tasks
  where
    filePath = "exportedFiles/tasks.csv"
