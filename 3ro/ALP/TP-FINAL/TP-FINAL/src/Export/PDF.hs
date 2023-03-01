module Export.PDF
  ( export
  ) where

import Data.Text
import Graphics.PDF
import Prelude as P
import Structures.Task

-- Exporta las tareas a un archivo PDF
export :: String -> [Task] -> IO ()
export folderName ts = do
  font <- getFont Helvetica
  let rect = PDFRect 0 0 widht height
  runPdf
    route
    (standardDocInfo {author = toPDFString "System", compressed = False})
    rect $ do myDocument font folderName (widht, height - 30) ts
  where
    route = "exportedFiles/tasks.pdf"
    widht = 450
    defaultHeight = 700
    height' = fromIntegral $ 30 + (P.length ts) * 30
    height =
      if height' > defaultHeight
        then height'
        else defaultHeight

-- Crea el documento PDF
myDocument :: AnyFont -> String -> (Double, Double) -> [Task] -> PDF ()
myDocument _ _ _ [] = return ()
myDocument font folderName (widht, height) ts = do
  page <- addPage Nothing
  drawWithPage page $ do
    drawText $ do
      setFont (PDFFont font 15)
      textStart ((widht / 2) - 85) height
      renderMode FillText
      displayText $ toPDFString $ "Folder '" ++ folderName ++ "' tasks"
    drawText $ do
      setFont (PDFFont font 10)
      textStart 10 (height - 15)
      renderMode FillText
      displayText $
        toPDFString "Name: Description - Priority - Date - Completed"
  newSection (toPDFString "Tasks") Nothing Nothing $ do
    createPageContent font (height - 30) i page ts
  where
    i = 1

-- Crea el contenido de la pagina a partir de las tareas recibidas
createPageContent ::
     AnyFont -> Double -> Integer -> PDFReference PDFPage -> [Task] -> PDF ()
createPageContent _ _ _ _ [] = return ()
createPageContent font height i page (t:ts) = do
  createPageContent' font height i page t
  createPageContent font (height - 15) (i + 1) page ts

-- FUncion auxiliar que va creando el contenido de la pagina
createPageContent' ::
     AnyFont -> Double -> Integer -> PDFReference PDFPage -> Task -> PDF ()
createPageContent' font height i page task =
  drawWithPage page $ do
    drawText $ do
      setFont (PDFFont font 10)
      textStart 10 height
      renderMode FillText
      displayText $ toPDFString ((formatTask i task))

-- Formatea la tarea para mostrarla en el PDF
formatTask :: Integer -> Task -> String
formatTask i task =
  show i ++
  ". " ++
  (tname task) ++
  ": " ++
  (description task) ++
  " - " ++
  (show $ priority task) ++
  " - " ++ (show $ date task) ++ " - " ++ (show' $ completed task)
  where
    show' True = "Completed"
    show' False = "Not completed"

-- Funcion para obtener la fuente
getFont :: FontName -> IO AnyFont
getFont fontName = do
  font <- mkStdFont fontName
  case font of
    Right f -> return f
    Left _ -> error "Error al cargar la fuente"

-- Funcion para convertir un String a Data.Text.Text
toPDFString :: String -> Data.Text.Text
toPDFString s = Data.Text.pack s
