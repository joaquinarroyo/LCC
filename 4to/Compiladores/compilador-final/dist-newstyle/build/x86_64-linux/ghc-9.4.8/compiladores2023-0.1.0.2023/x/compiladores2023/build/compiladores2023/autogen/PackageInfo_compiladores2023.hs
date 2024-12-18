{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_compiladores2023 (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "compiladores2023"
version :: Version
version = Version [0,1,0,2023] []

synopsis :: String
synopsis = "C\243digo fuente para la materia Compiladores (FCEIA/UNR)"
copyright :: String
copyright = "2023 Mauro Jaskelioff y Guido Martinez"
homepage :: String
homepage = "https://github.com/ compiladores-lcc/compiladores#readme"
