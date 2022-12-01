main = do
        putStrLn "Ingresa un numero:"
        s <- getLine
        if read s == num
        then putStrLn "Adivinaste!"
        else putStrLn "No adivinaste!" >>= \_ -> main
    where
        num = 5