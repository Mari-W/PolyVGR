module Parser where

import Ast ( Expr(Let), Type(TVar), Val(VUnit, VVar, VChan) )
import Result ()
import System.IO ()
import Control.Monad ()
import Text.ParserCombinators.Parsec
    ( alphaNum, letter, (<|>), parse )
import Text.ParserCombinators.Parsec.Expr ()
import Text.ParserCombinators.Parsec.Language ( emptyDef )
import qualified Text.ParserCombinators.Parsec.Token as Token

langDef = emptyDef {
    Token.commentLine   = "//",
    Token.identStart    = letter,
    Token.identLetter   = alphaNum,
    Token.reservedNames = [ "Type", 
                            "Session", 
                            "State", 
                            "Shape", 
                            "Dom",
                            "λ",
                            "\\", 
                            "∀",
                            "all",
                            "forall",
                            "∃",
                            "ex",
                            "exists",
                            "Chan",
                            "Unit", 
                            "End",  
                            "I",
                            "𝕀",
                            "X",
                            "𝕏",
                            "let", 
                            "in",
                            "proj", 
                            "left",
                            "π₁",
                            "right",
                            "π₂",
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
                            "new",
                            "chan",
                            "Λ",
                            "unit"],
    Token.reservedOpNames = [ "->",
                              "→",
                              "=>",
                              "⇒",
                              "↦",
                              "x",
                              "×",
                              ":",
                              ";", 
                              "+",
                              "⊕", 
                              "&",
                              "~",   
                              ",", 
                              "#",
                              "="]
}

lexer = Token.makeTokenParser langDef
identifier = Token.identifier lexer
reserved   = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens lexer
braces     = Token.braces lexer
brackets   = Token.brackets lexer
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
