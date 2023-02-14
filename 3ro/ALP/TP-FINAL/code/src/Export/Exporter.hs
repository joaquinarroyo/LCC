module Export.Exporter
  ( Export.Exporter.export
  , FileType(..)
  ) where

import Export.CSV as C (export)
import Export.PDF as P (export)
import Extra.Pp (Message, printMessage)
import Structures.Task (Task (..))

data FileType
  = PDF
  | CSV
  deriving (Eq, Show)

-- Funcion que exporta las tareas a un archivo segun el tipo recibido
export :: FileType -> String -> [Task] -> IO Message
export PDF folderName ts = P.export folderName ts >> message PDF
export CSV folderName ts = C.export folderName ts >> message CSV

message :: FileType -> IO Message
message fl = return $ printMessage $ "Tasks exported to tasks." ++ show fl
 