{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_TP_FINAL (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/bin"
libdir     = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/lib/x86_64-linux-ghc-9.2.5/TP-FINAL-0.1.0.0-AGh19s2qTBXDLQ05w5WuoN"
dynlibdir  = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/lib/x86_64-linux-ghc-9.2.5"
datadir    = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/share/x86_64-linux-ghc-9.2.5/TP-FINAL-0.1.0.0"
libexecdir = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/libexec/x86_64-linux-ghc-9.2.5/TP-FINAL-0.1.0.0"
sysconfdir = "/home/joaquin/Escritorio/facultad/3ro/ALP/TP-FINAL-ALP/TP-FINAL/.stack-work/install/x86_64-linux-tinfo6/f2c54474930789aaf579ff0138d0058e816ada6ed3f4bae1d1a69150aa48d94f/9.2.5/etc"

getBinDir     = catchIO (getEnv "TP_FINAL_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "TP_FINAL_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "TP_FINAL_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "TP_FINAL_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "TP_FINAL_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "TP_FINAL_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
