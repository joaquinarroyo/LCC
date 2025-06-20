{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-
  Module      : Main
  Description : Compilador de FD4.
  Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2023.
  License     : GPL-3
  Maintainer  : mauro@fceia.unr.edu.ar
  Stability   : experimental
-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.List.Split ( splitOn )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe, fromJust )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabSDecl, elabSynTy, elabDecl )
import Eval ( eval )
import PPrint ( pp , ppTy )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import System.CPUTime ( getCPUTime )

import CEK ( seek )
import Bytecompile ( bcWrite, bcRead, runBC, bytecompile )
import Bytecompile8 ( bcWrite8, bcRead8, runBC8, bytecompile8 )
import Optimizer ( optimize, deadCodeElimination )
import C
import ClosureConvert
import Profile ( Profile(..) )

prompt :: String
prompt = "FD4> "

-- | Parser de banderas
parseMode :: Parser (Mode, Bool, Bool)
parseMode = (,,) <$>
  (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
  <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
  <|> flag' CEK (long "cek" <> short 'e' <> help "Ejecutar en la CEK")
  <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
  <|> flag' Bytecompile8 (long "bytecompile8" <> short 'n' <> help "Compilar a la BVM8")
  <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
  <|> flag' RunVM8 (long "runVM8" <> short '8' <> help "Ejecutar bytecode8 en la BVM")
  <|> flag' Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
  <|> flag' Eval (long "eval" <> short 'e' <> help "Evaluar programa")
  <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
    )
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "profile" <> short 'p' <> help "Muestra datos de profilling")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode, Bool, Bool, [FilePath])
parseArgs = (\(a,b, c) d -> (a, b, c, d)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2023" )

    go :: (Mode, Bool, Bool, [FilePath]) -> IO ()
    go (Interactive, opt, pro, files) = runOrFail (Conf opt pro Interactive) (runInputT defaultSettings (repl files))
    go (InteractiveCEK, opt, pro, files) = runOrFail (Conf opt pro InteractiveCEK) (runInputT defaultSettings (repl files))
    go (RunVM, opt, pro, files) = runOrFail (Conf opt pro RunVM) $ mapM_ runVM files
    go (RunVM8, opt, pro, files) = runOrFail (Conf opt pro RunVM8) $ mapM_ runVM8 files
    go (m, opt, pro, files) = runOrFail (Conf opt pro m) $ mapM_ compileFile files

runOrFail :: Show a => Conf -> FD4 a -> IO ()
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> do
      if pro c && v /= NoneProfile
        then do
          print v
          return ()
        else return ()

-- | Corre el intérprete interactivo (loop principal)
repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
  lift $ setInter True
  lift $ catchErrors $ mapM_ compileFile args
  s <- lift get
  m <- lift getMode
  opt <- lift getOpt
  pro <- lift getPro
  when (inter s) $ liftIO $ putStrLn
    ( "Entorno interactivo para FD4. \n"
    ++ "Modo: " ++ show m ++ ", optimization: " ++ show opt ++ ", profilling: " ++ show pro ++ "\n"
    ++ "Escriba :? para recibir ayuda.")
  loop
  where
    loop = do
      minput <- getInputLine prompt
      case minput of
        Nothing -> return ()
        Just "" -> loop
        Just x -> do
          c <- liftIO $ interpretCommand x
          b <- lift $ catchErrors $ handleCommand c
          maybe loop (`when` loop) b

-- | Carga un archivo
loadFile ::  MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
  let filename = reverse (dropWhile isSpace (reverse f))
  x <- liftIO $ catch (readFile filename)
              (\e -> do let err = show (e :: IOException)
                        hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                        return "")
  setLastFile filename
  parseIO filename program x

-- | Compila un archivo
compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
  i <- getInter
  setInter False
  m <- getMode
  decls <- loadFile f
  mdecls <- mapM elabSDecl decls
  odecls <- mapM optimizeDecl (filter (/= Nothing) mdecls)
  opt <- getOpt
  odecls' <- if opt then deadCodeElimination odecls else return odecls
  edecls <- mapM evalDecl odecls'
  case m of
    Bytecompile -> do
      bytecode <- bytecompile edecls
      liftIO $ bcWrite bytecode bcfout
      printFD4 ("Compilacion exitosa a " ++ bcfout)
    Bytecompile8 -> do
      bytecode8 <- bytecompile8 edecls
      liftIO $ bcWrite8 bytecode8 bc8fout
      printFD4 ("Compilacion exitosa a " ++ bc8fout)
    CC -> do
      let code = runCC edecls
      let ccode = ir2C code
      liftIO $ ccWrite ccode cfout
      printFD4 ("Compilacion exitosa a " ++ cfout)
    Typecheck -> printFD4 "Typecheck exitoso"
    _ -> return ()
  setInter i
  where
    splitF = head $ splitOn "." f
    bcfout = splitF ++ ".bc"
    bc8fout = splitF ++ ".bc8"
    cfout = splitF ++ ".c"

-- | Parsea un archivo
parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x =
  case runP p x filename of
    Left e  -> throwError (ParseErr e)
    Right r -> return r

-- | Maneja una declaración superficial
optimizeDecl ::  MonadFD4 m => Maybe (Decl STerm) -> m (Decl TTerm)
optimizeDecl decl = do
  m <- getMode
  let decl' = elabDecl (fromJust decl)
  case m of
    Typecheck -> do
      decl' <- tcDecl decl'
      addDecl decl'
      return decl'
    _ -> optDecl decl'
  where
    optDecl :: MonadFD4 m => Decl Term -> m (Decl TTerm)
    optDecl d = do
      tdecl <- tcDecl d
      addDecl tdecl
      opt <- getOpt
      odecl <- if opt then optimize tdecl else return tdecl -- optimization
      return odecl

-- |
evalDecl :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
evalDecl decl = do
  m <- getMode
  case m of
    Interactive -> evalDecl' eval decl
    InteractiveCEK -> evalDecl' seek decl
    Eval -> evalDecl' eval decl
    CEK -> evalDecl' seek decl
    Bytecompile -> evalDecl' return decl
    Bytecompile8 -> evalDecl' return decl
    CC -> evalDecl' return decl
    _ -> return decl
  where
    evalDecl' :: MonadFD4 m => (TTerm -> m TTerm) -> Decl TTerm -> m (Decl TTerm)
    evalDecl' f d = do
      let t = declBody d
      ttt <- pp t
      t' <- f t
      let decl = d { declBody = t' }
      addDecl decl
      return decl

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive    String
                 | CompileFile           String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
--   indicando si se debe salir del programa o no.
handleCommand :: MonadFD4 m => Command -> m Bool
handleCommand cmd = do
  s@GlEnv {..} <- get
  case cmd of
    Quit   ->  return False
    Noop   ->  return True
    Help   ->  printFD4 (helpTxt commands) >> return True
    Browse ->  do
      printFD4 (unlines (reverse (nub (map declName glb))))
      return True
    Compile c -> do
      case c of
        CompileInteractive e -> compilePhrase e
        CompileFile f -> compileFile f
      return True
    Reload   ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
    PPrint e -> printPhrase e >> return True
    Type e   -> typeCheckPhrase e >> return True

-- | Procesa una expresión
compilePhrase :: MonadFD4 m => String -> m ()
compilePhrase x = do
  dot <- parseIO "<interactive>" declOrTm x
  case dot of
    Left d  -> do
      d' <- elabSDecl d
      d'' <- optimizeDecl d'
      evalDecl d''
      return ()
      -- void $ evalDecl (optimizeDecl d)
    Right t -> handleTerm t

-- | Evalua un término superficial
handleTerm :: MonadFD4 m => STerm -> m ()
handleTerm t = do
  m <- getMode
  t' <- elabSynTy t
  let t'' = elab t'
  s <- get
  tt <- tc t'' (tyEnv s)
  te <- case m of
    Interactive     -> eval tt
    InteractiveCEK  -> seek tt
  ppte <- pp te
  printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

-- | Imprime un término
printPhrase :: MonadFD4 m => String -> m ()
printPhrase x = do
  x' <- parseIO "<interactive>" tm x
  let ex = elab x'
  tyenv <- gets tyEnv
  tex <- tc ex tyenv
  t  <- case x' of
    (SV p f) -> fromMaybe tex <$> lookupDecl f
    _         -> return tex
  printFD4 "STerm:"
  printFD4 (show x')
  printFD4 "TTerm:"
  printFD4 (show t)

-- | Chequea el tipo de una expresión
typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
  t <- parseIO "<interactive>" tm x
  let t' = elab t
  s <- get
  tt <- tc t' (tyEnv s)
  let ty = getTy tt
  printFD4 (ppTy ty)

-- | Ejecuta un archivo bytecode
runVM :: (MonadFD4 m, MonadIO m) => FilePath -> m ()
runVM f = do
  b <- liftIO $ bcRead f
  t1 <- liftIO getCPUTime
  runBC b
  t2 <- liftIO getCPUTime
  return ()

-- | Ejecuta un archivo bytecode8
runVM8 :: (MonadFD4 m, MonadIO m) => FilePath -> m ()
runVM8 f = do
  b <- liftIO $ bcRead8 f
  t1 <- liftIO getCPUTime
  runBC8 b
  t2 <- liftIO getCPUTime
  return ()
