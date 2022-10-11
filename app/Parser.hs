module Parser where

import Ast
import Result
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

langDef = emptyDef {
    Token.commentStart  = "/*", 
    Token.commentEnd    = "*/",
    Token.commentLine   = "//",
    Token.identStart    = letter,
    Token.identLetter   = alphaNum,
    Token.reservedNames = [ "Type", 
                            "Session", 
                            "State", 
                            "Shape", 
                            "Dom", 
                            "All", 
                            "Lam", 
                            "Chan", 
                            "Unit", 
                            "End", 
                            "Acc", 
                            "I", 
                            "X",
                            "lam", 
                            "let", 
                            "in", 
                            "fork", 
                            "accept", 
                            "request", 
                            "send", 
                            "on", 
                            "receive", 
                            "select", 
                            "case", 
                            "of", 
                            "close", 
                            "new" ],
    Token.reservedOpNames = [ ";", 
                              "@", 
                              "@@", 
                              "x", 
                              "+", 
                              "&", 
                              "'", 
                              ".1", 
                              ".2", 
                              ",", 
                              "#", 
                              "=", 
                              "->" ]
}

lexer = Token.makeTokenParser langDef
identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens lexer
whiteSpace = Token.whiteSpace lexer

parser = whiteSpace >> expr

{- environments -}


{- values -}
val = parens val <|> val'

val' = var <|> chan <|> unit 
    
var = do VVar <$> identifier

chan = do 
  reserved "Chan"
  VChan . TVar <$> identifier

lam = do 
  reserved "lam"
  


unit = do
  reserved "unit"
  return VUnit 

{- expressions -}
expr = parens expr <|> expr'

expr' = let'

let' = do 
  reserved "let"
  var <- identifier
  reservedOp "="
  exp <- expr
  reserved "in"
  Let var exp <$> expr

{- types -}

parseFile :: String -> IO Expr
parseFile file = do
  prog <- readFile file
  case parse expr "" prog of
    Left pe -> print pe >> fail "parse error"
    Right ex -> return ex
