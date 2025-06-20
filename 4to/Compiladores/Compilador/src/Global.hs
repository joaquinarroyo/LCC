{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | InteractiveCEK
  | CEK
  | Bytecompile
  | Bytecompile8
  | RunVM
  | RunVM8
  | CC
  -- | Canon
  -- | Assembler
  -- | Build
  deriving Show

data Conf = Conf {
  opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
  pro :: Bool,          --  ^ True, si estaa habilitado el profilling.
  mode :: Mode
}

-- |
data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  tysin :: [SDecl]      -- ^ Entorno con declaraciones de sinonimos de tipos
} deriving Show

-- | Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n ty b) -> (n, ty))  (glb g)

-- | Entorno de sinonimos de tipos
tySinEnv :: GlEnv -> [(Name, Ty)]
tySinEnv g = map (\(DirectTypeDecl _ n ty) -> (n, ty))  (tysin g)

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] []
