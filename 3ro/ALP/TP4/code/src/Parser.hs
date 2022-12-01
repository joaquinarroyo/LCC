{-# OPTIONS_GHC -w #-}
module Parser (parseComm) where
import AST
import Data.Char
import Control.Applicative(Applicative(..))
import Control.Monad (ap)
import Control.Exception
import System.IO.Unsafe

-- parser produced by Happy Version 1.19.5

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 (Comm)
	| HappyAbsSyn5 (Exp Int)
	| HappyAbsSyn7 (Exp Bool)

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

parseComm ::  String -> String -> Either SomeException Comm
parseComm _ s =   unsafePerformIO 
                . (try :: IO Comm -> IO (Either SomeException Comm)) 
                . evaluate $ parserComm s

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64 :: () => Int -> ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (HappyIdentity) HappyAbsSyn)

happyReduce_1,
 happyReduce_2,
 happyReduce_3,
 happyReduce_4,
 happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27 :: () => ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (HappyIdentity) HappyAbsSyn)

action_0 (15) = happyShift action_4
action_0 (27) = happyShift action_2
action_0 (31) = happyShift action_5
action_0 (33) = happyShift action_6
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (27) = happyShift action_2
action_1 _ = happyFail

action_2 _ = happyReduce_1

action_3 (28) = happyShift action_19
action_3 (34) = happyAccept
action_3 _ = happyFail

action_4 (17) = happyShift action_18
action_4 _ = happyFail

action_5 (9) = happyShift action_10
action_5 (13) = happyShift action_11
action_5 (15) = happyShift action_12
action_5 (16) = happyShift action_13
action_5 (18) = happyShift action_14
action_5 (19) = happyShift action_15
action_5 (26) = happyShift action_16
action_5 (5) = happyGoto action_7
action_5 (6) = happyGoto action_8
action_5 (7) = happyGoto action_17
action_5 _ = happyFail

action_6 (9) = happyShift action_10
action_6 (13) = happyShift action_11
action_6 (15) = happyShift action_12
action_6 (16) = happyShift action_13
action_6 (18) = happyShift action_14
action_6 (19) = happyShift action_15
action_6 (26) = happyShift action_16
action_6 (5) = happyGoto action_7
action_6 (6) = happyGoto action_8
action_6 (7) = happyGoto action_9
action_6 _ = happyFail

action_7 (8) = happyShift action_33
action_7 (9) = happyShift action_34
action_7 (10) = happyShift action_35
action_7 (11) = happyShift action_36
action_7 (12) = happyShift action_37
action_7 (20) = happyShift action_38
action_7 (21) = happyShift action_39
action_7 (22) = happyShift action_40
action_7 (23) = happyShift action_41
action_7 _ = happyFail

action_8 _ = happyReduce_7

action_9 (24) = happyShift action_23
action_9 (25) = happyShift action_24
action_9 (29) = happyShift action_32
action_9 _ = happyFail

action_10 (9) = happyShift action_10
action_10 (13) = happyShift action_22
action_10 (15) = happyShift action_31
action_10 (16) = happyShift action_13
action_10 (6) = happyGoto action_30
action_10 _ = happyFail

action_11 (9) = happyShift action_10
action_11 (13) = happyShift action_11
action_11 (15) = happyShift action_12
action_11 (16) = happyShift action_13
action_11 (18) = happyShift action_14
action_11 (19) = happyShift action_15
action_11 (26) = happyShift action_16
action_11 (5) = happyGoto action_28
action_11 (6) = happyGoto action_8
action_11 (7) = happyGoto action_29
action_11 _ = happyFail

action_12 (17) = happyShift action_27
action_12 _ = happyReduce_14

action_13 _ = happyReduce_15

action_14 _ = happyReduce_18

action_15 _ = happyReduce_19

action_16 (9) = happyShift action_10
action_16 (13) = happyShift action_11
action_16 (15) = happyShift action_12
action_16 (16) = happyShift action_13
action_16 (18) = happyShift action_14
action_16 (19) = happyShift action_15
action_16 (26) = happyShift action_16
action_16 (5) = happyGoto action_7
action_16 (6) = happyGoto action_8
action_16 (7) = happyGoto action_26
action_16 _ = happyFail

action_17 (24) = happyShift action_23
action_17 (25) = happyShift action_24
action_17 (29) = happyShift action_25
action_17 _ = happyFail

action_18 (9) = happyShift action_10
action_18 (13) = happyShift action_22
action_18 (15) = happyShift action_12
action_18 (16) = happyShift action_13
action_18 (5) = happyGoto action_21
action_18 (6) = happyGoto action_8
action_18 _ = happyFail

action_19 (15) = happyShift action_4
action_19 (27) = happyShift action_2
action_19 (31) = happyShift action_5
action_19 (33) = happyShift action_6
action_19 (4) = happyGoto action_20
action_19 _ = happyFail

action_20 _ = happyReduce_3

action_21 (8) = happyShift action_33
action_21 (9) = happyShift action_34
action_21 (10) = happyShift action_35
action_21 (11) = happyShift action_36
action_21 (12) = happyShift action_37
action_21 _ = happyReduce_2

action_22 (9) = happyShift action_10
action_22 (13) = happyShift action_22
action_22 (15) = happyShift action_12
action_22 (16) = happyShift action_13
action_22 (5) = happyGoto action_58
action_22 (6) = happyGoto action_8
action_22 _ = happyFail

action_23 (9) = happyShift action_10
action_23 (13) = happyShift action_11
action_23 (15) = happyShift action_12
action_23 (16) = happyShift action_13
action_23 (18) = happyShift action_14
action_23 (19) = happyShift action_15
action_23 (26) = happyShift action_16
action_23 (5) = happyGoto action_7
action_23 (6) = happyGoto action_8
action_23 (7) = happyGoto action_57
action_23 _ = happyFail

action_24 (9) = happyShift action_10
action_24 (13) = happyShift action_11
action_24 (15) = happyShift action_12
action_24 (16) = happyShift action_13
action_24 (18) = happyShift action_14
action_24 (19) = happyShift action_15
action_24 (26) = happyShift action_16
action_24 (5) = happyGoto action_7
action_24 (6) = happyGoto action_8
action_24 (7) = happyGoto action_56
action_24 _ = happyFail

action_25 (15) = happyShift action_4
action_25 (27) = happyShift action_2
action_25 (31) = happyShift action_5
action_25 (33) = happyShift action_6
action_25 (4) = happyGoto action_55
action_25 _ = happyFail

action_26 _ = happyReduce_26

action_27 (9) = happyShift action_10
action_27 (13) = happyShift action_22
action_27 (15) = happyShift action_12
action_27 (16) = happyShift action_13
action_27 (5) = happyGoto action_54
action_27 (6) = happyGoto action_8
action_27 _ = happyFail

action_28 (8) = happyShift action_33
action_28 (9) = happyShift action_34
action_28 (10) = happyShift action_35
action_28 (11) = happyShift action_36
action_28 (12) = happyShift action_37
action_28 (14) = happyShift action_53
action_28 (20) = happyShift action_38
action_28 (21) = happyShift action_39
action_28 (22) = happyShift action_40
action_28 (23) = happyShift action_41
action_28 _ = happyFail

action_29 (14) = happyShift action_52
action_29 (24) = happyShift action_23
action_29 (25) = happyShift action_24
action_29 _ = happyFail

action_30 _ = happyReduce_17

action_31 _ = happyReduce_14

action_32 (15) = happyShift action_4
action_32 (27) = happyShift action_2
action_32 (31) = happyShift action_5
action_32 (33) = happyShift action_6
action_32 (4) = happyGoto action_51
action_32 _ = happyFail

action_33 (9) = happyShift action_10
action_33 (13) = happyShift action_22
action_33 (15) = happyShift action_12
action_33 (16) = happyShift action_13
action_33 (5) = happyGoto action_50
action_33 (6) = happyGoto action_8
action_33 _ = happyFail

action_34 (9) = happyShift action_10
action_34 (13) = happyShift action_22
action_34 (15) = happyShift action_12
action_34 (16) = happyShift action_13
action_34 (5) = happyGoto action_49
action_34 (6) = happyGoto action_8
action_34 _ = happyFail

action_35 (9) = happyShift action_10
action_35 (13) = happyShift action_22
action_35 (15) = happyShift action_12
action_35 (16) = happyShift action_13
action_35 (5) = happyGoto action_48
action_35 (6) = happyGoto action_8
action_35 _ = happyFail

action_36 (9) = happyShift action_10
action_36 (13) = happyShift action_22
action_36 (15) = happyShift action_12
action_36 (16) = happyShift action_13
action_36 (5) = happyGoto action_47
action_36 (6) = happyGoto action_8
action_36 _ = happyFail

action_37 (9) = happyShift action_10
action_37 (13) = happyShift action_22
action_37 (15) = happyShift action_12
action_37 (16) = happyShift action_13
action_37 (5) = happyGoto action_46
action_37 (6) = happyGoto action_8
action_37 _ = happyFail

action_38 (9) = happyShift action_10
action_38 (13) = happyShift action_22
action_38 (15) = happyShift action_12
action_38 (16) = happyShift action_13
action_38 (5) = happyGoto action_45
action_38 (6) = happyGoto action_8
action_38 _ = happyFail

action_39 (9) = happyShift action_10
action_39 (13) = happyShift action_22
action_39 (15) = happyShift action_12
action_39 (16) = happyShift action_13
action_39 (5) = happyGoto action_44
action_39 (6) = happyGoto action_8
action_39 _ = happyFail

action_40 (9) = happyShift action_10
action_40 (13) = happyShift action_22
action_40 (15) = happyShift action_12
action_40 (16) = happyShift action_13
action_40 (5) = happyGoto action_43
action_40 (6) = happyGoto action_8
action_40 _ = happyFail

action_41 (9) = happyShift action_10
action_41 (13) = happyShift action_22
action_41 (15) = happyShift action_12
action_41 (16) = happyShift action_13
action_41 (5) = happyGoto action_42
action_41 (6) = happyGoto action_8
action_41 _ = happyFail

action_42 (8) = happyShift action_33
action_42 (9) = happyShift action_34
action_42 (10) = happyShift action_35
action_42 (11) = happyShift action_36
action_42 (12) = happyShift action_37
action_42 _ = happyReduce_22

action_43 (8) = happyShift action_33
action_43 (9) = happyShift action_34
action_43 (10) = happyShift action_35
action_43 (11) = happyShift action_36
action_43 (12) = happyShift action_37
action_43 _ = happyReduce_23

action_44 (8) = happyShift action_33
action_44 (9) = happyShift action_34
action_44 (10) = happyShift action_35
action_44 (11) = happyShift action_36
action_44 (12) = happyShift action_37
action_44 _ = happyReduce_21

action_45 (8) = happyShift action_33
action_45 (9) = happyShift action_34
action_45 (10) = happyShift action_35
action_45 (11) = happyShift action_36
action_45 (12) = happyShift action_37
action_45 _ = happyReduce_20

action_46 (8) = happyShift action_33
action_46 (9) = happyShift action_34
action_46 (10) = happyShift action_35
action_46 (11) = happyShift action_36
action_46 _ = happyReduce_9

action_47 _ = happyReduce_13

action_48 _ = happyReduce_12

action_49 (10) = happyShift action_35
action_49 (11) = happyShift action_36
action_49 _ = happyReduce_11

action_50 (10) = happyShift action_35
action_50 (11) = happyShift action_36
action_50 _ = happyReduce_10

action_51 (28) = happyShift action_19
action_51 (30) = happyShift action_60
action_51 _ = happyFail

action_52 _ = happyReduce_27

action_53 _ = happyReduce_16

action_54 (8) = happyShift action_33
action_54 (9) = happyShift action_34
action_54 (10) = happyShift action_35
action_54 (11) = happyShift action_36
action_54 _ = happyReduce_8

action_55 (28) = happyShift action_19
action_55 (30) = happyShift action_59
action_55 _ = happyFail

action_56 (24) = happyShift action_23
action_56 _ = happyReduce_25

action_57 _ = happyReduce_24

action_58 (8) = happyShift action_33
action_58 (9) = happyShift action_34
action_58 (10) = happyShift action_35
action_58 (11) = happyShift action_36
action_58 (12) = happyShift action_37
action_58 (14) = happyShift action_53
action_58 _ = happyFail

action_59 (32) = happyShift action_61
action_59 _ = happyReduce_4

action_60 _ = happyReduce_6

action_61 (29) = happyShift action_62
action_61 _ = happyFail

action_62 (15) = happyShift action_4
action_62 (27) = happyShift action_2
action_62 (31) = happyShift action_5
action_62 (33) = happyShift action_6
action_62 (4) = happyGoto action_63
action_62 _ = happyFail

action_63 (28) = happyShift action_19
action_63 (30) = happyShift action_64
action_63 _ = happyFail

action_64 _ = happyReduce_5

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 _
	 =  HappyAbsSyn4
		 (Skip
	)

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn5  happy_var_3)
	_
	(HappyTerminal (TVar happy_var_1))
	 =  HappyAbsSyn4
		 (Let happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_3  4 happyReduction_3
happyReduction_3 (HappyAbsSyn4  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn4
		 (Seq happy_var_1 happy_var_3
	)
happyReduction_3 _ _ _  = notHappyAtAll 

happyReduce_4 = happyReduce 5 4 happyReduction_4
happyReduction_4 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (IfThenElse happy_var_2 happy_var_4 Skip
	) `HappyStk` happyRest

happyReduce_5 = happyReduce 9 4 happyReduction_5
happyReduction_5 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (IfThenElse happy_var_2 happy_var_4 happy_var_8
	) `HappyStk` happyRest

happyReduce_6 = happyReduce 5 4 happyReduction_6
happyReduction_6 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (While happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_1  5 happyReduction_7
happyReduction_7 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_3  5 happyReduction_8
happyReduction_8 (HappyAbsSyn5  happy_var_3)
	_
	(HappyTerminal (TVar happy_var_1))
	 =  HappyAbsSyn5
		 (EAssgn happy_var_1 happy_var_3
	)
happyReduction_8 _ _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_3  5 happyReduction_9
happyReduction_9 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (ESeq happy_var_1 happy_var_3
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  5 happyReduction_10
happyReduction_10 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (Plus happy_var_1 happy_var_3
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_3  5 happyReduction_11
happyReduction_11 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (Minus happy_var_1 happy_var_3
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_3  5 happyReduction_12
happyReduction_12 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (Times happy_var_1 happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_3  5 happyReduction_13
happyReduction_13 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (Div happy_var_1 happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  6 happyReduction_14
happyReduction_14 (HappyTerminal (TVar happy_var_1))
	 =  HappyAbsSyn5
		 (Var happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  6 happyReduction_15
happyReduction_15 (HappyTerminal (TNum happy_var_1))
	 =  HappyAbsSyn5
		 (Const happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  6 happyReduction_16
happyReduction_16 _
	(HappyAbsSyn5  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (happy_var_2
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_2  6 happyReduction_17
happyReduction_17 (HappyAbsSyn5  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (UMinus happy_var_2
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  7 happyReduction_18
happyReduction_18 _
	 =  HappyAbsSyn7
		 (BTrue
	)

happyReduce_19 = happySpecReduce_1  7 happyReduction_19
happyReduction_19 _
	 =  HappyAbsSyn7
		 (BFalse
	)

happyReduce_20 = happySpecReduce_3  7 happyReduction_20
happyReduction_20 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn7
		 (Eq happy_var_1 happy_var_3
	)
happyReduction_20 _ _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_3  7 happyReduction_21
happyReduction_21 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn7
		 (NEq happy_var_1 happy_var_3
	)
happyReduction_21 _ _ _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_3  7 happyReduction_22
happyReduction_22 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn7
		 (Gt happy_var_1 happy_var_3
	)
happyReduction_22 _ _ _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_3  7 happyReduction_23
happyReduction_23 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn7
		 (Lt happy_var_1 happy_var_3
	)
happyReduction_23 _ _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_3  7 happyReduction_24
happyReduction_24 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (And happy_var_1 happy_var_3
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_3  7 happyReduction_25
happyReduction_25 (HappyAbsSyn7  happy_var_3)
	_
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn7
		 (Or happy_var_1 happy_var_3
	)
happyReduction_25 _ _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_2  7 happyReduction_26
happyReduction_26 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (Not happy_var_2
	)
happyReduction_26 _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_3  7 happyReduction_27
happyReduction_27 _
	(HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn7
		 (happy_var_2
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 34 34 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TPlus -> cont 8;
	TMinus -> cont 9;
	TTimes -> cont 10;
	TDiv -> cont 11;
	TComma -> cont 12;
	TOpen -> cont 13;
	TClose -> cont 14;
	TVar happy_dollar_dollar -> cont 15;
	TNum happy_dollar_dollar -> cont 16;
	TAss -> cont 17;
	TTrue -> cont 18;
	TFalse -> cont 19;
	TEq -> cont 20;
	TNEq -> cont 21;
	TLt -> cont 22;
	TGt -> cont 23;
	TAnd -> cont 24;
	TOr -> cont 25;
	TNot -> cont 26;
	TSkip -> cont 27;
	TSeq -> cont 28;
	TBOpen -> cont 29;
	TBClose -> cont 30;
	TIf -> cont 31;
	TElse -> cont 32;
	TWhile -> cont 33;
	_ -> happyError' (tk:tks)
	}

happyError_ 34 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = return
    (<*>) = ap
instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(Token)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

parser tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Error sintactico"

data Token = TVar Variable
       | TNum Int
       | TPlus
       | TMinus
       | TTimes 
       | TDiv
       | TComma
       | TOpen
       | TClose
       | TTrue
       | TFalse
       | TEq
       | TNEq
       | TLt
       | TGt
       | TAnd
       | TOr
       | TNot 
       | TBOpen
       | TBClose
       | TAss
       | TSkip
       | TSeq
       | TIf
       | TElse
       | TWhile
 deriving Show

-- Analizador Lexicografico
lexer :: String -> [Token]
lexer [] = []
lexer (c:cs) 
      | isSpace c = lexer cs
      | isAlpha c = lexAlpha (c:cs)
      | isDigit c = lexNum (c:cs)
lexer ('/':('/':cs)) = lexer (dropWhile (/= '\n') cs)      
lexer ('=':('=':cs)) = TEq : lexer cs
lexer ('=':cs)  = TAss : lexer cs
lexer ('-':cs)  = TMinus : lexer cs
lexer ('+':cs)  = TPlus : lexer cs
lexer ('*':cs)  = TTimes : lexer cs
lexer ('/':cs)  = TDiv : lexer cs
lexer (',':cs)  = TComma : lexer cs
lexer ('{':cs)  = TBOpen : lexer cs
lexer ('}':cs)  = TBClose : lexer cs
lexer ('(':cs)  = TOpen : lexer cs
lexer (')':cs)  = TClose : lexer cs
lexer ('!':('=':cs)) = TNEq : lexer cs
lexer ('<':cs)  = TLt : lexer cs
lexer ('>':cs)  = TGt : lexer cs
lexer ('!':cs)  = TNot : lexer cs
lexer ('&':('&':cs)) = TAnd : lexer cs
lexer ('|':('|':cs)) = TOr : lexer cs
lexer (';':cs)  = TSeq : lexer cs

lexAlpha cs =
   case span isAlpha cs of
	    ("true",rest)  -> TTrue : lexer rest
	    ("false",rest) -> TFalse : lexer rest
	    ("skip",rest)  -> TSkip : lexer rest
	    ("if",rest)    -> TIf : lexer rest
	    ("else",rest)  -> TElse : lexer rest    
	    ("while",rest) -> TWhile : lexer rest
	    (var,rest)     -> TVar var : lexer rest

lexNum :: String -> [Token]
lexNum cs = TNum (readNum num) : lexer rest
      where (num,rest) = span isDigit cs

readNum :: String -> Int
readNum ds = foldl1 (\n d -> 10 * n + d) (map digToInt ds)
	     where digToInt d = fromEnum d - fromEnum '0'

parserComm = parser . lexer
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 8 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4










































{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "/usr/lib/ghc/include/ghcversion.h" #-}

















{-# LINE 8 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates/GenericTemplate.hs" #-}

{-# LINE 46 "templates/GenericTemplate.hs" #-}








{-# LINE 67 "templates/GenericTemplate.hs" #-}

{-# LINE 77 "templates/GenericTemplate.hs" #-}

{-# LINE 86 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 155 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 256 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 322 "templates/GenericTemplate.hs" #-}
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
