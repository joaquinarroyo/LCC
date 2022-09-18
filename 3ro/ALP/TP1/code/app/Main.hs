module Main where

import           Parser                         ( parseComm )
import           System.Console.GetOpt
import qualified System.Environment            as Env
import           System.Exit
import           Control.Monad                  ( when )
import           PPLis

import qualified Eval1                         as E1
import qualified Eval2                         as E2
import qualified Eval3                         as E3

---------------------------------------------------------

data Options = Options
  { optPrint :: Bool
  , optAST   :: Bool
  , optEval  :: Int
  , optHelp  :: Bool
  }
  deriving Show

defaultOptions :: Options
defaultOptions =
  Options { optPrint = False, optAST = False, optEval = 0, optHelp = False }

options :: [OptDescr (Options -> Options)]
options =
  [ Option ['p']
           ["print"]
           (NoArg (\opts -> opts { optPrint = True }))
           "Imprimir el programa de entrada."
  , Option ['a']
           ["AST"]
           (NoArg (\opts -> opts { optAST = True }))
           "Mostrar el AST del programa de entrada."
  , Option ['e']
           ["evaluator"]
           (ReqArg (\s opts -> opts { optEval = read s }) "N_EVALUADOR")
           "Elegir evaluador 1, 2 o 3."
  , Option ['h']
           ["help"]
           (NoArg (\opts -> opts { optHelp = True }))
           "Imprimir guia de uso."
  ]

finalOptions :: [String] -> IO (Options, [String])
finalOptions argv = case getOpt Permute options argv of
  (o, n, []  ) -> return (foldl (flip id) defaultOptions o, n)
  (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))
  where header = "Uso:"

main :: IO ()
main = do
  s : opts   <- Env.getArgs
  (opts', _) <- finalOptions opts
  runOptions s opts'

runOptions :: FilePath -> Options -> IO ()
runOptions fp opts
  | optHelp opts = putStrLn (usageInfo "Uso: " options)
  | otherwise = do
    s <- readFile fp
    case parseComm fp s of
      Left  error -> print error
      Right ast   -> if
        | optAST opts       -> print ast
        | optPrint opts     -> putStrLn (renderComm ast)
        | optEval opts == 1 -> print (E1.eval ast)
        | optEval opts == 2 -> print (E2.eval ast)
        | optEval opts == 3 -> print (E3.eval ast)
        | otherwise         -> print (E1.eval ast)

