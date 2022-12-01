import Data.Char

main :: IO()
main = do putStrLn "Ingresa nombre de archivo de entrada:"
          s1 <- getLine
          c <- readFile s1
          putStrLn "Ingresa nombre de archivo de salida:"
          s2 <- getLine
          writeFile s2 (map toUpper c)
          putStrLn "Archivo convertido a mayusculas!"
        
upper :: String -> String
upper [] = []
upper (x:xs) = toUpper x : upper xs
    