{-# OPTIONS_GHC -w #-}
{-# OPTIONS -XMagicHash -XBangPatterns -XTypeSynonymInstances -XFlexibleInstances -cpp #-}
#if __GLASGOW_HASKELL__ >= 710
{-# OPTIONS_GHC -XPartialTypeSignatures #-}
#endif
module Parser.Parser where

import Command.AST 
import Data.Char
import Data.Maybe
import Export.Exporter
import Extra.Lib as L
import Extra.Pp
import Filter.AST
import Monad.Env
import Structures.Folder
import Structures.Route
import Structures.Task
import Data.Time (parseTimeM, defaultTimeLocale)
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import qualified GHC.Exts as Happy_GHC_Exts
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.0

newtype HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn5 :: t5 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn5 #-}
happyOut5 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t5
happyOut5 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut5 #-}
happyIn6 :: t6 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn6 #-}
happyOut6 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t6
happyOut6 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut6 #-}
happyIn7 :: t7 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn7 #-}
happyOut7 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t7
happyOut7 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut7 #-}
happyIn8 :: t8 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn8 #-}
happyOut8 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t8
happyOut8 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut8 #-}
happyIn9 :: t9 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn9 #-}
happyOut9 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t9
happyOut9 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut9 #-}
happyIn10 :: t10 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn10 #-}
happyOut10 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t10
happyOut10 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut10 #-}
happyIn11 :: t11 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn11 #-}
happyOut11 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t11
happyOut11 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut11 #-}
happyIn12 :: t12 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn12 #-}
happyOut12 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t12
happyOut12 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut12 #-}
happyIn13 :: t13 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t13
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: t14 -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> t14
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyInTok :: (Token) -> (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14)
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12 t13 t14) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyExpList :: HappyAddr
happyExpList = HappyA# "\x00\x00\x01\x3e\x02\x00\x00\x00\x00\x00\x00\x00\xc0\xfd\x79\x1e\x00\x00\x00\x00\x20\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x20\x00\x00\x00\x00\x00\x04\xf8\x08\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc0\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03\x00\x00\x00\x00\x40\x00\x40\x00\x00\x08\x00\x00\x80\x00\x1f\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x04\x00\x00\x00\x00\x00\xe2\x01\x02\x00\x00\x00\x00\x00\xf1\x00\x01\x00\x00\x00\x00\x00\x02\x7c\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x24\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x20\x01\x00\x00\x00\x00\x00\x00\x90\x00\x00\x00\x00\x00\x00\x00\x48\x00\x00\x00\x00\x00\x00\x00\x24\x00\x00\x00\x00\x00\x00\x00\x12\x00\x00\x00\x00\x00\x00\x00\x09\x00\x00\x00\x00\x00\x00\x80\x04\x00\x00\x00\x00\x00\x00\x80\x01\x00\x00\x00\x00\x00\x00\xc0\x00\x00\x00\x00\x00\x04\x00\x03\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x20\xc0\x47\x00\x00\x00\x00\x00\x10\xe0\x23\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x60\x00\x00\x00\x00\x00\x20\xc0\x47\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x80\x0f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x40\x00\x00\x00\x00\x00\x00\x00\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x80\x01\x00\x00\x00\x00\x00\x00\x20\x01\x00\x00\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x40\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x80\x04\x00\x00\x00\x00\x00\x00\x40\x02\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x82\x00\x00\x00\x00\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x10\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x08\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_term","%start_comm","Comm","Route","Exp","Field","Oration","DateNull","Date","Num","Bool","FileType","'='","':'","'('","')'","'>'","'<'","\">=\"","\"<=\"","'/'","','","\"..\"","NAME","DESCRIPTION","COMPLETED","PRIORITY","DATE","NEQ","AND","OR","NOT","VAR","NUM","TRUE","FALSE","NULL","NEWTASK","DELETETASK","EDITTASK","SET","COMPLETETASK","NEWDIR","EDITDIR","DELETEDIR","LS","CD","SEARCH","REC","ILIKE","EXIT","SAVE","LOAD","EXPORT","PDF","CSV","NEWPROFILE","DELETEPROFILE","SHOWPROFILES","HELP","%eof"]
        bit_start = st Prelude.* 63
        bit_end = (st Prelude.+ 1) Prelude.* 63
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..62]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x37\x00\x0f\x00\xed\xff\x38\x00\xf4\xff\x3f\x00\x35\x00\x35\x00\x35\x00\x35\x00\x35\x00\x35\x00\x00\x00\xf6\xff\x07\x00\x00\x00\x00\x00\x42\x00\xf8\xff\x57\x00\x00\x00\x00\x00\x00\x00\xf1\xff\x01\x00\x37\x00\x00\x00\x00\x00\x10\x00\x08\x00\x17\x00\x37\x00\x00\x00\xef\xff\x59\x00\x59\x00\x59\x00\x59\x00\xef\xff\x3b\x00\x3b\x00\x3b\x00\x3b\x00\x3b\x00\x3b\x00\x29\x00\x29\x00\x22\x00\x5b\x00\x5b\x00\x5b\x00\x37\x00\x37\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x36\x00\x37\x00\x00\x00\x00\x00\x69\x00\x00\x00\x60\x00\x00\x00\x00\x00\x00\x00\x54\x00\x00\x00\x61\x00\x61\x00\x6a\x00\x6d\x00\x40\x00\x00\x00\xf6\xff\x36\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x6f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x63\x00\x00\x00\x65\x00\x65\x00\x41\x00\x3b\x00\x6b\x00\x6e\x00\x6e\x00\x71\x00\x02\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x73\x00\x6c\x00\x00\x00\x3c\x00\x3d\x00\x74\x00\x79\x00\x16\x00\x76\x00\x70\x00\x7e\x00\x00\x00\x72\x00\x00\x00\x80\x00\x75\x00\x00\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x58\x00\x85\x00\x00\x00\x00\x00\x00\x00\x00\x00\x83\x00\x86\x00\x88\x00\x89\x00\x8a\x00\x8b\x00\x00\x00\x8f\x00\x5a\x00\x00\x00\x00\x00\x00\x00\x8c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x5c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x5e\x00\x00\x00\x5d\x00\x8d\x00\x8e\x00\x90\x00\x91\x00\x5f\x00\x82\x00\x92\x00\x93\x00\x94\x00\x95\x00\x96\x00\x97\x00\x98\x00\x00\x00\x9a\x00\x9d\x00\x9e\x00\x64\x00\x66\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x68\x00\x00\x00\x00\x00\x00\x00\x00\x00\x9f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa0\x00\xa1\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa5\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xa3\x00\xa4\x00\xa2\x00\xa6\x00\xa8\x00\xa7\x00\xab\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x67\x00\xa9\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xac\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyAdjustOffset :: Happy_GHC_Exts.Int# -> Happy_GHC_Exts.Int#
happyAdjustOffset off = off

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xef\xff\x00\x00\x00\x00\xeb\xff\xe9\xff\x00\x00\x00\x00\x00\x00\xe5\xff\xe4\xff\xea\xff\x00\x00\x00\x00\x00\x00\xcb\xff\xca\xff\x00\x00\x00\x00\x00\x00\x00\x00\xcd\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe6\xff\xe7\xff\xbf\xff\xbe\xff\xe8\xff\xec\xff\x00\x00\xee\xff\xe1\xff\xe2\xff\xf0\xff\xc8\xff\xf1\xff\xf2\xff\xf3\xff\x00\x00\xf9\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc9\xff\x00\x00\xed\xff\xce\xff\xcf\xff\xdc\xff\xdb\xff\xe0\xff\xcc\xff\xda\xff\xc1\xff\xc0\xff\xdf\xff\xd9\xff\xc3\xff\xc2\xff\xd4\xff\xd5\xff\xd6\xff\xd7\xff\xde\xff\xd8\xff\xc7\xff\x00\x00\xc6\xff\xd0\xff\xd1\xff\xd2\xff\xd3\xff\xdd\xff\x00\x00\xe3\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf4\xff\xf5\xff\xf6\xff\xf8\xff\xf7\xff\x00\x00\x00\x00\xfa\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xc3\xff\xc4\xff\x00\x00\xfc\xff\x00\x00\xfb\xff\x00\x00\x00\x00\xc5\xff\xfd\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x0b\x00\x01\x00\x12\x00\x13\x00\x16\x00\x04\x00\x1a\x00\x19\x00\x01\x00\x03\x00\x15\x00\x0a\x00\x05\x00\x06\x00\x07\x00\x08\x00\x01\x00\x11\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x01\x00\x11\x00\x04\x00\x14\x00\x05\x00\x06\x00\x07\x00\x08\x00\x0a\x00\x11\x00\x31\x00\x2b\x00\x2c\x00\x31\x00\x04\x00\x26\x00\x11\x00\x1a\x00\x1b\x00\x1c\x00\x25\x00\x1e\x00\x1f\x00\x20\x00\x21\x00\x22\x00\x23\x00\x24\x00\x12\x00\x13\x00\x27\x00\x28\x00\x29\x00\x2a\x00\x03\x00\x03\x00\x2d\x00\x2e\x00\x2f\x00\x30\x00\x17\x00\x18\x00\x03\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x12\x00\x13\x00\x15\x00\x14\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x10\x00\x16\x00\x16\x00\x16\x00\x19\x00\x19\x00\x19\x00\x15\x00\x17\x00\x18\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x05\x00\x06\x00\x05\x00\x06\x00\x02\x00\x03\x00\x02\x00\x03\x00\x02\x00\x03\x00\x15\x00\x06\x00\x07\x00\x16\x00\x15\x00\x1d\x00\x09\x00\xff\xff\x0a\x00\x15\x00\x15\x00\x0a\x00\x09\x00\x16\x00\x15\x00\x0a\x00\x09\x00\x04\x00\x0a\x00\x09\x00\x02\x00\x16\x00\x16\x00\x15\x00\x04\x00\x00\x00\x16\x00\x04\x00\x16\x00\x07\x00\x04\x00\x16\x00\x04\x00\x04\x00\x04\x00\x04\x00\x01\x00\xff\xff\xff\xff\x06\x00\x06\x00\x09\x00\x06\x00\x06\x00\xff\xff\x07\x00\x07\x00\x07\x00\x07\x00\x07\x00\x04\x00\x08\x00\x08\x00\x04\x00\x04\x00\x04\x00\x04\x00\x04\x00\x01\x00\x04\x00\x04\x00\xff\xff\x08\x00\x04\x00\xff\xff\x07\x00\x06\x00\x04\x00\x07\x00\xff\xff\x06\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x3e\x00\x31\x00\x34\x00\x35\x00\x63\x00\x7c\x00\x04\x00\x64\x00\x28\x00\x1a\x00\x3f\x00\x7d\x00\x29\x00\x2a\x00\x2b\x00\x2c\x00\x2e\x00\x32\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x22\x00\x2d\x00\x85\x00\x20\x00\x23\x00\x24\x00\x25\x00\x26\x00\x86\x00\x2f\x00\xff\xff\x38\x00\x39\x00\xff\xff\x54\x00\x33\x00\x27\x00\x06\x00\x07\x00\x08\x00\x3c\x00\x09\x00\x0a\x00\x0b\x00\x0c\x00\x0d\x00\x0e\x00\x0f\x00\x34\x00\x35\x00\x10\x00\x11\x00\x12\x00\x13\x00\x1a\x00\x48\x00\x14\x00\x15\x00\x16\x00\x17\x00\x56\x00\x57\x00\x47\x00\x1b\x00\x1c\x00\x1d\x00\x1e\x00\x1f\x00\x34\x00\x35\x00\x41\x00\x20\x00\x6c\x00\x6d\x00\x6e\x00\x6f\x00\x70\x00\x5a\x00\x82\x00\x5a\x00\x5b\x00\x5b\x00\x5b\x00\x3a\x00\x56\x00\x57\x00\x17\x00\x18\x00\x3a\x00\x18\x00\x2f\x00\x18\x00\x20\x00\x18\x00\x68\x00\x61\x00\x60\x00\x61\x00\x4f\x00\x18\x00\x4e\x00\x18\x00\x4d\x00\x18\x00\x36\x00\x7f\x00\x80\x00\x63\x00\x41\x00\x4b\x00\x4d\x00\x00\x00\x72\x00\x41\x00\x41\x00\x71\x00\x6a\x00\x7a\x00\x41\x00\x7e\x00\x7b\x00\x87\x00\x86\x00\x6a\x00\x89\x00\x63\x00\x83\x00\x41\x00\x8b\x00\x04\x00\x84\x00\x45\x00\x63\x00\x5f\x00\x44\x00\x8a\x00\x43\x00\x42\x00\x41\x00\x3f\x00\x3c\x00\x00\x00\x00\x00\x67\x00\x66\x00\x36\x00\x65\x00\x64\x00\x00\x00\x5e\x00\x5d\x00\x5c\x00\x5b\x00\x58\x00\x52\x00\x57\x00\x54\x00\x51\x00\x50\x00\x4b\x00\x49\x00\x48\x00\x6a\x00\x78\x00\x77\x00\x00\x00\x76\x00\x73\x00\x00\x00\x75\x00\x74\x00\x72\x00\x7e\x00\x00\x00\x87\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (2, 65) [
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65)
	]

happy_n_terms = 50 :: Prelude.Int
happy_n_nonterms = 10 :: Prelude.Int

#if __GLASGOW_HASKELL__ >= 710
happyReduce_2 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_2 = happyReduce 10# 0# happyReduction_2
happyReduction_2 (happy_x_10 `HappyStk`
	happy_x_9 `HappyStk`
	happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_3 of { happy_var_3 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	case happyOut12 happy_x_7 of { happy_var_7 -> 
	case happyOut11 happy_x_9 of { happy_var_9 -> 
	happyIn5
		 (NewTask happy_var_3 happy_var_5 (P happy_var_7) happy_var_9
	) `HappyStk` happyRest}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_3 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_3 = happyReduce 8# 0# happyReduction_3
happyReduction_3 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_3 of { happy_var_3 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	case happyOut12 happy_x_7 of { happy_var_7 -> 
	happyIn5
		 (NewTask happy_var_3 happy_var_5 (P happy_var_7) Null
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_4 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_4 = happyReduce 8# 0# happyReduction_4
happyReduction_4 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_3 of { happy_var_3 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	case happyOut11 happy_x_7 of { happy_var_7 -> 
	happyIn5
		 (NewTask happy_var_3 happy_var_5 (P 0) happy_var_7
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_5 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_5 = happyReduce 6# 0# happyReduction_5
happyReduction_5 (happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_3 of { happy_var_3 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (NewTask happy_var_3 happy_var_5 (P 0) Null
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_6 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_6 = happySpecReduce_2  0# happyReduction_6
happyReduction_6 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (DeleteTask happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_7 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_7 = happyReduce 5# 0# happyReduction_7
happyReduction_7 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_2 of { happy_var_2 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (EditTaskDescription happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_8 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_8 = happyReduce 5# 0# happyReduction_8
happyReduction_8 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_2 of { happy_var_2 -> 
	case happyOut9 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (EditTaskName happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_9 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_9 = happyReduce 5# 0# happyReduction_9
happyReduction_9 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_2 of { happy_var_2 -> 
	case happyOut13 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (EditTaskCompleted happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_10 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_10 = happyReduce 5# 0# happyReduction_10
happyReduction_10 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_2 of { happy_var_2 -> 
	case happyOut12 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (EditTaskPriority happy_var_2 (P happy_var_5)
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_11 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_11 = happyReduce 5# 0# happyReduction_11
happyReduction_11 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut9 happy_x_2 of { happy_var_2 -> 
	case happyOut11 happy_x_5 of { happy_var_5 -> 
	happyIn5
		 (EditTaskDate happy_var_2 happy_var_5
	) `HappyStk` happyRest}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_12 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_12 = happySpecReduce_2  0# happyReduction_12
happyReduction_12 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (EditTaskCompleted happy_var_2 True
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_13 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_13 = happySpecReduce_2  0# happyReduction_13
happyReduction_13 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (NewDir happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_14 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_14 = happySpecReduce_2  0# happyReduction_14
happyReduction_14 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (EditDir happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_15 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_15 = happySpecReduce_2  0# happyReduction_15
happyReduction_15 happy_x_2
	happy_x_1
	 =  case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (DeleteDir happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_16 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_16 = happySpecReduce_1  0# happyReduction_16
happyReduction_16 happy_x_1
	 =  happyIn5
		 (LS
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_17 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_17 = happySpecReduce_2  0# happyReduction_17
happyReduction_17 happy_x_2
	happy_x_1
	 =  case happyOut6 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (CD happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_18 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_18 = happySpecReduce_3  0# happyReduction_18
happyReduction_18 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_3 of { happy_var_3 -> 
	happyIn5
		 (Search happy_var_3 True
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_19 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_19 = happySpecReduce_2  0# happyReduction_19
happyReduction_19 happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (Search happy_var_2 False
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_20 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_20 = happySpecReduce_1  0# happyReduction_20
happyReduction_20 happy_x_1
	 =  happyIn5
		 (Exit
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_21 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_21 = happySpecReduce_1  0# happyReduction_21
happyReduction_21 happy_x_1
	 =  happyIn5
		 (Help
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_22 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_22 = happySpecReduce_1  0# happyReduction_22
happyReduction_22 happy_x_1
	 =  happyIn5
		 (SaveProfile
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_23 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_23 = happySpecReduce_2  0# happyReduction_23
happyReduction_23 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TVar happy_var_2) -> 
	happyIn5
		 (LoadProfile happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_24 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_24 = happySpecReduce_2  0# happyReduction_24
happyReduction_24 happy_x_2
	happy_x_1
	 =  case happyOut14 happy_x_2 of { happy_var_2 -> 
	happyIn5
		 (Export happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_25 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_25 = happySpecReduce_2  0# happyReduction_25
happyReduction_25 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_2 of { (TVar happy_var_2) -> 
	happyIn5
		 (NewProfile happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_26 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_26 = happySpecReduce_1  0# happyReduction_26
happyReduction_26 happy_x_1
	 =  happyIn5
		 (DeleteProfile
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_27 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_27 = happySpecReduce_1  0# happyReduction_27
happyReduction_27 happy_x_1
	 =  happyIn5
		 (ShowProfiles
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_28 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_28 = happySpecReduce_3  1# happyReduction_28
happyReduction_28 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TVar happy_var_1) -> 
	case happyOut6 happy_x_3 of { happy_var_3 -> 
	happyIn6
		 (Route happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_29 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_29 = happySpecReduce_1  1# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TVar happy_var_1) -> 
	happyIn6
		 (Route happy_var_1 Empty
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_30 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_30 = happySpecReduce_1  1# happyReduction_30
happyReduction_30 happy_x_1
	 =  happyIn6
		 (Back
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_31 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_31 = happySpecReduce_3  2# happyReduction_31
happyReduction_31 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	case happyOut9 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldEq happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_32 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_32 = happySpecReduce_3  2# happyReduction_32
happyReduction_32 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldEqB happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_33 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_33 = happySpecReduce_3  2# happyReduction_33
happyReduction_33 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldEqP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_34 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_34 = happySpecReduce_3  2# happyReduction_34
happyReduction_34 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldEqT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_35 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_35 = happySpecReduce_3  2# happyReduction_35
happyReduction_35 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	case happyOut9 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldIlike happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_36 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_36 = happySpecReduce_3  2# happyReduction_36
happyReduction_36 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut8 happy_x_1 of { happy_var_1 -> 
	case happyOut9 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldNEq happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_37 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_37 = happySpecReduce_3  2# happyReduction_37
happyReduction_37 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut13 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldNEqB happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_38 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_38 = happySpecReduce_3  2# happyReduction_38
happyReduction_38 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldNEqP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_39 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_39 = happySpecReduce_3  2# happyReduction_39
happyReduction_39 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut10 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldNEqT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_40 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_40 = happySpecReduce_3  2# happyReduction_40
happyReduction_40 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldGtP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_41 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_41 = happySpecReduce_3  2# happyReduction_41
happyReduction_41 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldLtP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_42 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_42 = happySpecReduce_3  2# happyReduction_42
happyReduction_42 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldGteP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_43 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_43 = happySpecReduce_3  2# happyReduction_43
happyReduction_43 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut12 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldLteP (P happy_var_3)
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_44 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_44 = happySpecReduce_3  2# happyReduction_44
happyReduction_44 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldGtT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_45 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_45 = happySpecReduce_3  2# happyReduction_45
happyReduction_45 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldLtT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_46 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_46 = happySpecReduce_3  2# happyReduction_46
happyReduction_46 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldGteT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_47 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_47 = happySpecReduce_3  2# happyReduction_47
happyReduction_47 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut11 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (FieldLteT happy_var_3
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_48 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_48 = happySpecReduce_3  2# happyReduction_48
happyReduction_48 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	case happyOut7 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (And happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_49 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_49 = happySpecReduce_3  2# happyReduction_49
happyReduction_49 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_1 of { happy_var_1 -> 
	case happyOut7 happy_x_3 of { happy_var_3 -> 
	happyIn7
		 (Or happy_var_1 happy_var_3
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_50 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_50 = happySpecReduce_2  2# happyReduction_50
happyReduction_50 happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_2 of { happy_var_2 -> 
	happyIn7
		 (Not happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_51 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_51 = happySpecReduce_3  2# happyReduction_51
happyReduction_51 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut7 happy_x_2 of { happy_var_2 -> 
	happyIn7
		 (happy_var_2
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_52 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_52 = happySpecReduce_1  3# happyReduction_52
happyReduction_52 happy_x_1
	 =  happyIn8
		 (Name
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_53 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_53 = happySpecReduce_1  3# happyReduction_53
happyReduction_53 happy_x_1
	 =  happyIn8
		 (Description
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_54 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_54 = happySpecReduce_2  4# happyReduction_54
happyReduction_54 happy_x_2
	happy_x_1
	 =  case happyOutTok happy_x_1 of { (TVar happy_var_1) -> 
	case happyOut9 happy_x_2 of { happy_var_2 -> 
	happyIn9
		 (happy_var_1 ++ " " ++ happy_var_2
	)}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_55 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_55 = happySpecReduce_1  4# happyReduction_55
happyReduction_55 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TVar happy_var_1) -> 
	happyIn9
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_56 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_56 = happySpecReduce_1  5# happyReduction_56
happyReduction_56 happy_x_1
	 =  case happyOut11 happy_x_1 of { happy_var_1 -> 
	happyIn10
		 (happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_57 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_57 = happySpecReduce_1  5# happyReduction_57
happyReduction_57 happy_x_1
	 =  happyIn10
		 (Null
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_58 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_58 = happyReduce 8# 6# happyReduction_58
happyReduction_58 (happy_x_8 `HappyStk`
	happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TNum happy_var_5) -> 
	case happyOutTok happy_x_6 of { (TNum happy_var_6) -> 
	case happyOutTok happy_x_8 of { (TNum happy_var_8) -> 
	happyIn11
		 (L.localTime (happy_var_1 ++ "-" ++ happy_var_3 ++ "-" ++ happy_var_5 ++ " " ++ happy_var_6 ++ ":" ++ happy_var_8)
	) `HappyStk` happyRest}}}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_59 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_59 = happyReduce 5# 6# happyReduction_59
happyReduction_59 (happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOutTok happy_x_1 of { (TNum happy_var_1) -> 
	case happyOutTok happy_x_3 of { (TNum happy_var_3) -> 
	case happyOutTok happy_x_5 of { (TNum happy_var_5) -> 
	happyIn11
		 (L.localTime (happy_var_1 ++ "-" ++ happy_var_3 ++ "-" ++ happy_var_5)
	) `HappyStk` happyRest}}}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_60 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_60 = happySpecReduce_1  7# happyReduction_60
happyReduction_60 happy_x_1
	 =  case happyOutTok happy_x_1 of { (TNum happy_var_1) -> 
	happyIn12
		 (read happy_var_1
	)}

#if __GLASGOW_HASKELL__ >= 710
happyReduce_61 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_61 = happySpecReduce_1  7# happyReduction_61
happyReduction_61 happy_x_1
	 =  happyIn12
		 (0
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_62 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_62 = happySpecReduce_1  8# happyReduction_62
happyReduction_62 happy_x_1
	 =  happyIn13
		 (True
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_63 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_63 = happySpecReduce_1  8# happyReduction_63
happyReduction_63 happy_x_1
	 =  happyIn13
		 (False
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_64 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_64 = happySpecReduce_1  9# happyReduction_64
happyReduction_64 happy_x_1
	 =  happyIn14
		 (PDF
	)

#if __GLASGOW_HASKELL__ >= 710
happyReduce_65 :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)
#endif
happyReduce_65 = happySpecReduce_1  9# happyReduction_65
happyReduction_65 happy_x_1
	 =  happyIn14
		 (CSV
	)

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = happyDoAction i tk action sts stk in
	case tk of {
	TEOF -> happyDoAction 49# tk action sts stk;
	TEquals -> cont 1#;
	TColon -> cont 2#;
	TOpen -> cont 3#;
	TClose -> cont 4#;
	TGt -> cont 5#;
	TLt -> cont 6#;
	TGte -> cont 7#;
	TLte -> cont 8#;
	TSlash -> cont 9#;
	TComma -> cont 10#;
	TBack -> cont 11#;
	TName -> cont 12#;
	TDescription -> cont 13#;
	TCompleted -> cont 14#;
	TPriority -> cont 15#;
	TDate -> cont 16#;
	TNequals -> cont 17#;
	TAnd -> cont 18#;
	TOr -> cont 19#;
	TNot -> cont 20#;
	TVar happy_dollar_dollar -> cont 21#;
	TNum happy_dollar_dollar -> cont 22#;
	TTrue -> cont 23#;
	TFalse -> cont 24#;
	TNull -> cont 25#;
	TNewTask -> cont 26#;
	TDeleteTask -> cont 27#;
	TEditTask -> cont 28#;
	TSet -> cont 29#;
	TCompleteTask -> cont 30#;
	TNewDir -> cont 31#;
	TEditDir -> cont 32#;
	TDeleteDir -> cont 33#;
	TLS -> cont 34#;
	TCD -> cont 35#;
	TSearch -> cont 36#;
	TRec -> cont 37#;
	TILike -> cont 38#;
	TExit -> cont 39#;
	TSave -> cont 40#;
	TLoad -> cont 41#;
	TExport -> cont 42#;
	TPDF -> cont 43#;
	TCSV -> cont 44#;
	TNewProfile -> cont 45#;
	TDeleteProfile -> cont 46#;
	TShowProfiles -> cont 47#;
	THelp -> cont 48#;
	_ -> happyError' (tk, [])
	})

happyError_ explist 49# tk = happyError' (tk, explist)
happyError_ explist _ tk = happyError' (tk, explist)

happyThen :: () => P a -> (a -> P b) -> P b
happyThen = (thenP)
happyReturn :: () => a -> P a
happyReturn = (returnP)
#if __GLASGOW_HASKELL__ >= 710
happyParse :: () => Happy_GHC_Exts.Int# -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)

happyNewToken :: () => Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)

happyDoAction :: () => Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _)

happyReduceArr :: () => Happy_Data_Array.Array Prelude.Int (Happy_GHC_Exts.Int# -> Token -> Happy_GHC_Exts.Int# -> Happy_IntList -> HappyStk (HappyAbsSyn _ _ _ _ _ _ _ _ _ _) -> P (HappyAbsSyn _ _ _ _ _ _ _ _ _ _))

#endif
happyThen1 :: () => P a -> (a -> P b) -> P b
happyThen1 = happyThen
happyReturn1 :: () => a -> P a
happyReturn1 = happyReturn
happyError' :: () => ((Token), [Prelude.String]) -> P a
happyError' tk = (\(tokens, explist) -> happyError) tk
term = happySomeParser where
 happySomeParser = happyThen (happyParse 0#) (\x -> happyReturn (let {x' = happyOut7 x} in x'))

comm = happySomeParser where
 happySomeParser = happyThen (happyParse 1#) (\x -> happyReturn (let {x' = happyOut5 x} in x'))

happySeq = happyDontSeq


data ParseResult a = Ok a | Failed String deriving Show  

type LineNumber = Int
type P a = String -> LineNumber -> ParseResult a

getLineNo :: P LineNumber
getLineNo = \s l -> Ok l

thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \s l-> case m s l of
                         Ok a     -> k a s l
                         Failed e -> Failed e
                         
returnP :: a -> P a
returnP a = \s l-> Ok a

failP :: String -> P a
failP err = \s l -> Failed err

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s l -> case m s l of
                        Ok a     -> Ok a
                        Failed e -> k e s l

happyError :: P a
happyError = \ s i -> 
        Failed $ printHappyError ("Línea "++(show (i::LineNumber))++": Error de sintaxis "++ (s))

data Token =      TVar String
                | TNum String
                | TName
                | TDescription
                | TCompleted
                | TPriority
                | TDate
                | TAnd
                | TOr
                | TNot
                | TEquals
                | TOpen
                | TClose
                | TSlash
                | TColon
                | TComma
                | TBack
                | TNequals
                | TTrue
                | TFalse
                | TNull
                | TGt
                | TLt
                | TGte
                | TLte
                | TNewTask
                | TDeleteTask
                | TEditTask
                | TCompleteTask
                | TNewDir
                | TEditDir
                | TDeleteDir
                | TLS
                | TCD
                | TSearch
                | TRec
                | TILike
                | TExit
                | THelp
                | TSave
                | TLoad
                | TExport
                | TPDF
                | TCSV
                | TNewProfile
                | TDeleteProfile
                | TShowProfiles
                | TSet
                | TEOF
               deriving Show

----------------------------------
lexer cont s = case s of
                    [] -> cont TEOF []
                    ('\n':s)  ->  \line -> lexer cont s (line + 1)
                    (c:cs)
                          | isSpace c -> lexer cont cs
                          | c == '-' -> lexFlag (c:cs)
                          | isAlpha c -> lexVar (c:cs)
                          | isDigit c -> lexNum (c:cs)
                          | otherwise -> lexSym (c:cs)
                    unknown -> \line -> Failed $ 
                     "Línea "++(show line)++": No se puede reconocer "++(show $ take 10 unknown)++ "..."
                    where lexVar cs = case span isAlphaNum cs of
                              (s, rest) -> case L.toLower s of
                                        "name" -> cont TName rest
                                        "description" -> cont TDescription rest
                                        "completed" -> cont TCompleted rest
                                        "priority" -> cont TPriority rest
                                        "date" -> cont TDate rest
                                        "and" -> cont TAnd rest
                                        "or" -> cont TOr rest
                                        "not" -> cont TNot rest
                                        "true" -> cont TTrue rest
                                        "false" -> cont TFalse rest
                                        "null" -> cont TNull rest 
                                        "newtask" -> cont TNewTask rest
                                        "deletetask" -> cont TDeleteTask rest
                                        "edittask" -> cont TEditTask rest
                                        "completetask" -> cont TCompleteTask rest
                                        "newdir" -> cont TNewDir rest
                                        "editdir" -> cont TEditDir rest
                                        "deletedir" -> cont TDeleteDir rest
                                        "ls" -> cont TLS rest
                                        "cd" -> cont TCD rest
                                        "search" -> cont TSearch rest
                                        "ilike" -> cont TILike rest
                                        "exit" -> cont TExit rest
                                        "help" -> cont THelp rest
                                        "save" -> cont TSave rest
                                        "load" -> cont TLoad rest
                                        "export" -> cont TExport rest
                                        "pdf" -> cont TPDF rest
                                        "csv" -> cont TCSV rest
                                        "newprofile" -> cont TNewProfile rest
                                        "deleteprofile" -> cont TDeleteProfile rest
                                        "showprofiles" -> cont TShowProfiles rest
                                        "set" -> cont TSet rest
                                        _ -> cont (TVar s) rest
                          lexNum cs = case span isDigit cs of
                              (num,rest) -> cont (TNum num) rest
                          lexFlag cs = case span isFlag cs of
                              (s, rest) -> case L.toLower s of
                                        "-r" -> cont TRec rest
                                        _ -> cont (TVar s) rest
                              where isFlag c = c `elem` "-r"         
                          lexSym cs = case span isSymbol cs of
                              (">=", rest) -> cont TGte rest
                              ("<=", rest) -> cont TLte rest
                              ("=", rest) -> cont TEquals rest
                              ("(", rest) -> cont TOpen rest
                              (")", rest) -> cont TClose rest
                              ("/", rest) -> cont TSlash rest
                              (":", rest) -> cont TColon rest
                              (",", rest) -> cont TComma rest
                              ("..", rest) -> cont TBack rest
                              ("!=", rest) -> cont TNequals rest
                              (">", rest) -> cont TGt rest
                              ("<", rest) -> cont TLt rest
                              (sym, rest) -> cont (TVar sym) rest
                              where isSymbol c = c `elem` "!<>=/,:()."  
                                           
exp_parse s = term s 1
comm_parse s = comm s 1
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $













-- Do not remove this comment. Required to fix CPP parsing when using GCC and a clang-compiled alex.
#if __GLASGOW_HASKELL__ > 706
#define LT(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.<# m)) :: Prelude.Bool)
#define GTE(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.>=# m)) :: Prelude.Bool)
#define EQ(n,m) ((Happy_GHC_Exts.tagToEnum# (n Happy_GHC_Exts.==# m)) :: Prelude.Bool)
#else
#define LT(n,m) (n Happy_GHC_Exts.<# m)
#define GTE(n,m) (n Happy_GHC_Exts.>=# m)
#define EQ(n,m) (n Happy_GHC_Exts.==# m)
#endif



















data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
        (happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = {- nothing -}
          case action of
                0#           -> {- nothing -}
                                     happyFail (happyExpListPerState ((Happy_GHC_Exts.I# (st)) :: Prelude.Int)) i tk st
                -1#          -> {- nothing -}
                                     happyAccept i tk st
                n | LT(n,(0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}
                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
                n                 -> {- nothing -}
                                     happyShift new_state i tk st
                                     where new_state = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where off    = happyAdjustOffset (indexShortOffAddr happyActOffsets st)
         off_i  = (off Happy_GHC_Exts.+# i)
         check  = if GTE(off_i,(0# :: Happy_GHC_Exts.Int#))
                  then EQ(indexShortOffAddr happyCheck off_i, i)
                  else Prelude.False
         action
          | check     = indexShortOffAddr happyTable off_i
          | Prelude.otherwise = indexShortOffAddr happyDefActions st




indexShortOffAddr (HappyA# arr) off =
        Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#




{-# INLINE happyLt #-}
happyLt x y = LT(x,y)


readArrayBit arr bit =
    Bits.testBit (Happy_GHC_Exts.I# (indexShortOffAddr arr ((unbox_int bit) `Happy_GHC_Exts.iShiftRA#` 4#))) (bit `Prelude.mod` 16)
  where unbox_int (Happy_GHC_Exts.I# x) = x






data HappyAddr = HappyA# Happy_GHC_Exts.Addr#


-----------------------------------------------------------------------------
-- HappyState data type (not arrays)













-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail [] 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st1)
             off_i = (off Happy_GHC_Exts.+# nt)
             new_state = indexShortOffAddr happyTable off_i




          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where off = happyAdjustOffset (indexShortOffAddr happyGotoOffsets st)
         off_i = (off Happy_GHC_Exts.+# nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist 0# tk old_st _ stk@(x `HappyStk` _) =
     let i = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction 0# tk action sts ((Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
