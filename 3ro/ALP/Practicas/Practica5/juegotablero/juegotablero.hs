main = play tablero n
    where
        tablero = ["*****", "****", "***", "**", "*"]
        n = 0

play :: [String] -> Int -> IO ()
play tablero p = if win tablero then putStrLn ("Gano jugador " ++ winner ++ "!!!!")
                 else
                 do
                    printTablero tablero
                    putStrLn ("Jugador " ++ player)
                    putStrLn "Elegir fila a sacar: "
                    l <- getLine
                    putStrLn "Elegir cantidad de asteriscos a sacar: "
                    n <- getLine
                    play (sacarAsteriscos tablero (read l - 1) (read n)) (p+1)
    where
        player = show (rem p 2)
        winner = show (rem (p-1) 2)
                        

printTablero :: [String] -> IO ()
printTablero tablero = do
                        putStrLn "-------TABLERO--------"
                        printTablero' tablero n (n+1)
                        putStrLn "----------------------"
    where n = length tablero

printTablero' :: [String] -> Int -> Int -> IO ()
printTablero' [x] n m = putStrLn ((show (m-n)) ++ ":" ++ x)
printTablero' (x:xs) n m = putStrLn ((show (m-n)) ++ ":" ++ x) >>= \_ -> printTablero' xs (n-1) m

win :: [String] -> Bool
win [] = True
win (x:xs) = if x == "" then True && win xs else False

sacarAsteriscos :: [String] -> Int -> Int -> [String]
sacarAsteriscos [] _ _ = []
sacarAsteriscos (x:xs) 0 n = [sacarAsteriscos' x n] ++ xs
sacarAsteriscos (x:xs) m n = [x] ++ sacarAsteriscos xs (m-1) n

sacarAsteriscos' :: [Char] -> Int -> [Char]
sacarAsteriscos' [] _ = []
sacarAsteriscos' l 0 = l
sacarAsteriscos' (x:xs) n = sacarAsteriscos' xs (n-1)