{-# OPTIONS_GHC -Wnoncanonical-monoid-instances #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-noncanonical-monoid-instances #-}

module Profile where

import Global (Mode(..))

-- | Profile
data Profile = CEKProfile      { cekSteps :: Int } 
             | BytecodeProfile { bcOps :: Int, maxStackSize :: Int, clousures :: Int } 
             | NoneProfile

instance Semigroup Profile where
  (<>) = mappend

instance Monoid Profile where
  mempty                                                     = NoneProfile
  mappend NoneProfile NoneProfile                            = NoneProfile
  mappend NoneProfile p                                      = p
  mappend p NoneProfile                                      = p
  mappend (CEKProfile n) (CEKProfile m)                      = CEKProfile (n + m)
  mappend (BytecodeProfile n m k) (BytecodeProfile n' m' k') = BytecodeProfile (n + n') (max m m') (k + k')

instance Show Profile where
  show (CEKProfile n)           = "CEK PROFILE: steps = " ++ show n
  show (BytecodeProfile n m k)  = "Bytecode PROFILE: steps = " ++ show n ++ ", max stack size = " ++ show m ++ ", clousures = " ++ show k
  show NoneProfile              = ""

instance Eq Profile where
  (CEKProfile n) == (CEKProfile m)                 = n == m
  (BytecodeProfile n m k) == (BytecodeProfile n' m' k') = n == n' && m == m' && k == k'
  NoneProfile == NoneProfile                        = True
  _ == _                                            = False

getProfile :: Mode -> Profile
getProfile CEK    = CEKProfile 0
getProfile RunVM  = BytecodeProfile 0 0 0
getProfile RunVM8 = BytecodeProfile 0 0 0
getProfile _      = NoneProfile

tickProfile :: Mode -> Profile
tickProfile CEK     = CEKProfile 1
tickProfile RunVM   = BytecodeProfile 1 0 0
tickProfile RunVM8  = BytecodeProfile 1 0 0
tickProfile _       = NoneProfile

maxStackProfile :: Mode -> Int -> Profile
maxStackProfile RunVM s   = BytecodeProfile 0 s 0
maxStackProfile RunVM8 s  = BytecodeProfile 0 s 0
maxStackProfile m _       = NoneProfile

addClousureProfile :: Mode -> Int -> Profile
addClousureProfile RunVM c  = BytecodeProfile 0 0 c
addClousureProfile RunVM8 c = BytecodeProfile 0 0 c
addClousureProfile m _      = NoneProfile