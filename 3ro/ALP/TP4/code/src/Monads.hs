module Monads where

import           AST

-- Clases de mónadas que proveen las operaciones necesarias
-- para implementar los evaluadores.

-- Clase para representar mónadas con estado de variables
class Monad m => MonadState m where
    -- Busca el valor de una variable
    lookfor :: Variable -> m Int
    -- Cambia el valor de una variable
    update :: Variable -> Int -> m ()

-- Clase para representar mónadas que lanzan errores
class Monad m => MonadError m where
    -- Lanza un error
    throw :: Error -> m a

-- Ejercicio 3.b: Dar una clase que provea las operaciones necesarias para
-- llevar la traza de ejecución. Llamela MonadTrace.
class Monad m => MonadTrace m where
    -- Agraga mas elemenos a la traza
    add :: Trace -> m Trace