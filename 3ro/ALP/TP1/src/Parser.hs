module Parser where

import           Text.ParserCombinators.Parsec
import           Text.Parsec.Token
import           Text.Parsec.Language           ( emptyDef )
import           AST

-----------------------
-- Funcion para facilitar el testing del parser.
totParser :: Parser a -> Parser a
totParser p = do
  whiteSpace lis
  t <- p
  eof
  return t

-- Analizador de Tokens
lis :: TokenParser u
lis = makeTokenParser
  (emptyDef
    { commentStart    = "/*"
    , commentEnd      = "*/"
    , commentLine     = "//"
    , opLetter        = char '='
    , reservedNames   = ["true", "false", "if", "else", "while", "skip" , "do", "for"]
    , reservedOpNames = [ "+"
                        , "-"
                        , "*"
                        , "/"
                        , "<"
                        , ">"
                        , "&&"
                        , "||"
                        , "!"
                        , "="
                        , "=="
                        , "!="
                        , ";"
                        , ","
                        , "?"
                        , ":"
                        ]
    }
  )

-----------------------------------
-- Parser de expressiones enteras
-----------------------------------

addMinusOp = do {reservedOp lis "+"; return Plus}
         <|> do {reservedOp lis "-"; return Minus}

timesDivOp = do {reservedOp lis "*"; return Times}
        <|> do {reservedOp lis "/"; return Div}

intexp :: Parser (Exp Int)
intexp = ternParser

ternParser :: Parser (Exp Int)
ternParser = try (do b <- boolAtomParser
                     reservedOp lis "?"
                     i1 <- ternParser
                     reservedOp lis ":"
                     ECond b i1 <$> ternParser)
             <|>
             addMinusParser

addMinusParser :: Parser (Exp Int)
addMinusParser = timesDivParser `chainl1` addMinusOp

timesDivParser :: Parser (Exp Int)
timesDivParser  = intFactorParser  `chainl1` timesDivOp

intFactorParser :: Parser (Exp Int)
intFactorParser = parens lis intexp
                  <|>
                  try (do n <- natural lis
                          return (Const (fromIntegral n)))
                  <|>
                  try (do i <- identifier lis
                          return (Var i))
                  <|>
                  uMinusParser

uMinusParser :: Parser (Exp Int)
uMinusParser = do reservedOp lis "-"
                  UMinus <$> intFactorParser

-----------------------------------
-- Parser de expressiones booleanas
-----------------------------------

boolCompOp = do {reservedOp lis "==" ; return Eq}
         <|> do {reservedOp lis "!=" ; return NEq}
         <|> do {reservedOp lis "<" ; return Lt}
         <|> do {reservedOp lis ">" ; return Gt}

boolOp = do {reservedOp lis "&&" ; return And}
     <|> do {reservedOp lis "||" ; return Or}

boolexp :: Parser (Exp Bool)
boolexp = andOrParser

andOrParser :: Parser (Exp Bool)
andOrParser = boolCompParser `chainl1` boolOp

boolCompParser :: Parser (Exp Bool)
boolCompParser = try (do i1 <- intexp
                         b <- boolCompOp
                         b i1 <$> intexp)
                 <|>
                 boolAtomParser

boolAtomParser :: Parser (Exp Bool)
boolAtomParser = try (parens lis boolexp)
                 <|>
                 do reserved lis "true"
                    return BTrue
                 <|>
                 do reserved lis "false"
                    return BFalse
                 <|>
                 do reservedOp lis "!"
                    Not <$> boolAtomParser

-----------------------------------
-- Parser de comandos
-----------------------------------

semicolon = do {reservedOp lis ";" ; return Seq}

comm :: Parser Comm
comm = (skipParser
        <|> try letParser
        <|> ifThenParser
        <|> whileParser)
       `chainr1` semicolon

skipParser :: Parser Comm
skipParser = do reserved lis "skip"
                return Skip

letParser :: Parser Comm
letParser = do v <- identifier lis
               reservedOp lis "="
               Let v <$> intexp

ifThenParser :: Parser Comm
ifThenParser = do reserved lis "if"
                  b <- boolexp
                  c1 <- braces lis comm
                  IfThenElse b c1 <$> elseParser

elseParser :: Parser Comm
elseParser = do reserved lis "else"
                braces lis comm
             <|>
             return Skip

whileParser :: Parser Comm
whileParser = do reserved lis "while"
                 b <- boolexp
                 c <- braces lis comm
                 return (While b c)

------------------------------------
-- Función de parseo
------------------------------------
parseComm :: SourceName -> String -> Either ParseError Comm
parseComm = parse (totParser comm)
