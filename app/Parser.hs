{-# LANGUAGE FlexibleContexts, CPP #-}
module Parser where

import Ast
    ( Expr(..),
      Has(HasKind),
      Kind(KLam, KType, KSession, KState, KShape, KDom),
      Label(LRight, LLeft),
      Type(SSEmpty, TApp, TLam, EAll, EArr, EChan, EAcc, EUnit, EPair,
           SSend, SRecv, SChoice, SBranch, SEnd, SDual, SHEmpty, SHSingle,
           SHMerge, DEmpty, DProj, SSBind, DMerge, TVar),
      Val(VPair, VVar, VChan, VAbs, VTAbs, VUnit) )
import Result (Result, ok, raise)
import System.IO ()
import Control.Monad ()
import Text.ParserCombinators.Parsec
    ( alphaNum, letter, parse, spaces, string, many, char, many1, optional, space, noneOf, option, sepBy1, unexpected, try, eof, (<?>) )
import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec.Expr ()
import Text.ParserCombinators.Parsec.Language ( emptyDef )
import qualified Text.ParserCombinators.Parsec.Token as Token
import Debug.Trace ( trace )
import Data.List (isInfixOf)

#define tl trace (__FILE__ ++":"++ show __LINE__)

parseFile :: String -> IO (Result Expr)
parseFile file = do
  prog <- readFile file
  case parse (spaces *> expr1 <* spaces <* eof) "" prog of
    Left pe -> print pe >> fail "parse error"
    Right ex -> return (ok ex)

parseString :: String -> Result Expr
parseString s = do
  case parse (spaces *> expr1 <* spaces <* eof) "" s of
    Left pe -> raise "parse error"
    Right ex -> ok ex


{- keywords -}

kws = ["Type", "Session", "State", "Shape", "Dom", "left", "right", "proj1", "proj2", "all", "forall", "ex", "exists", "Chan", "Unit", "I", "X", "let", "in", "fork", "accept", "request", "send", "on", "receive", "select",  "case", "of", "close", "new", "chan", "unit"]
syms = ["->", "→", "=>", "⇒", "λ", "𝜆", "\\", "𝕀", "𝕏", "π₁", "π₂", "π", "Λ", "{", "}", "(", ")",  "[", "]",  "·", "*", "+", "⊕", "↦", ";", ":", "×", "#"]
kwFunArr = string "->" <|> string "→"
kwCstrArr = string "=>" <|> string "⇒"
kwTupTimes = char '*' <|> char '×'
kwLambda = char 'λ' <|> char '𝜆' <|> char '\\'
kwForall = string "all" <|> string "forall" <|> string "∀"
kwExists = string "ex" <|> string "exists" <|> string "∃"
kwShEmpty = char 'I' <|> char '𝕀'
kwShSingle = char 'X' <|> char '𝕏'
kwTLambda = char 'Λ' <|> char '\\'
kwProj1 = string "π₁" <|> string "proj1"
kwProj2 = string "π₂" <|> string "proj2"
kwLab1 = string "1" <|> string "left"
kwLab2 = string "2" <|> string "right"
kwStEmpty = string "{}" <|> string "·"
kwChoice = char '+' <|> char '⊕'
kwBind = string "->" <|> string "↦" <|> string "→"


{- util -}

l <|> r = try l P.<|> r 

surround cl cr r = do
  char cl
  spaces
  r_ <- try r
  spaces
  char cr
  return r_

brackets = tl $ surround '[' ']'

parens = tl $ surround '(' ')'

braces = tl $ surround '{' '}'

space1 = tl $ do
  space
  spaces

identifier = tl $ do
  s <- many1 alphaNum
  if s `elem` kws then 
    fail $ "identifier " ++ s ++ " is a reserved keyword"
  else
    if s `elem` syms then 
      fail $ "identifier " ++ s ++ " is a reserved symbol"
    else
      return s


{- kinds -}

kType = tl $ do
  string "Type"
  return KType

kSession = tl $ do
  string "Session"
  return KSession

kState = tl $ do
  string "State"
  return KState

kShape = tl $ do
  string "Shape"
  return KShape

kDom = tl $ do
  string "Dom"
  spaces
  KDom <$> type9

kLam = tl $ do
  d <- kind2
  spaces
  kwFunArr
  spaces
  KLam d <$> kind1

kind1 = tl $ kLam <|> kind2
kind2 = tl (kType P.<|> kSession P.<|> kState P.<|> kShape P.<|> kDom P.<|> parens kind1) <?> "kind"


{- labels -}

lLeft = tl $ do
  kwLab1
  return LLeft

lRight = tl $ do
  kwLab2
  return LRight

label = tl $lLeft P.<|> lRight

lProj1 = tl $ do
  kwProj1
  return LLeft

lProj2 = tl $ do
  kwProj2
  return LRight

lProj = tl $ lProj1 P.<|> lProj2


{- types -}

tVar = tl $ TVar <$> identifier

tApp = tl $ do
  f <- type9
  space1
  TApp f <$> type9

domBind = tl $ do
  id <- identifier
  spaces
  string ":"
  spaces
  d <- kDom
  return (id, d)

tLam = tl $ do
  kwLambda
  (id, d) <- parens domBind
  spaces
  string "."
  spaces
  TLam id d <$> type1

cstr = tl $ do
  t <- type1
  spaces
  string "#"
  spaces
  t_ <- type1
  return (t, t)
cstrs = tl $ do
  sepBy1 cstr (char ',')

kBind = tl $ do
  id <- identifier
  spaces
  string ":"
  spaces
  k <- kind1
  return (id, k)

eAll = tl $ do
  kwForall
  (id, k) <- parens kBind
  spaces
  string "."
  cs <- option [] (do
      cs <- parens cstrs
      spaces
      kwCstrArr
      return cs) <?> "constraints"
  spaces
  EAll id k cs <$> type1

ctxBind = tl $ do
  id <- identifier
  spaces
  char ':'
  spaces
  k <- kind1
  return (id, HasKind k)
ctxBinds = tl $ sepBy1 ctxBind (char ',')
ctxEmpty = tl $ do
  kwStEmpty
  return []
ctx1 = tl $ ctxEmpty P.<|> ctxBinds 

stTy = tl $ do
  st <- braces type1
  spaces
  char ';'
  spaces
  t <- type1
  return (st, t)

ctxStTy = tl $ do
  ctx <- option [] (do
    kwExists
    spaces
    ctx <- ctx1
    char '.'
    spaces
    return ctx) <?> "context"
  (st, t) <- stTy
  return (ctx, st, t)

eArr = tl $ parens $ do
  (st1, t1) <- stTy
  spaces
  kwFunArr
  (ctx, st2, t2) <- ctxStTy
  return (EArr st1 t1 ctx st2 t2)

eChan = tl $ do
  string "Chan"
  spaces
  EChan <$> type9

eAcc = tl $ EAcc <$> brackets type1

eUnit = tl $ do
  spaces
  string "Unit"
  return EUnit

eTup = tl $ do
  t <- type3
  spaces
  kwTupTimes
  spaces
  EPair t <$> type2

domStTy = tl $ do
  kwExists
  (id, d) <- domBind
  spaces
  char '.'
  spaces
  (st, t) <- stTy
  return (id, d, st, t)

sSend = tl $ do
  char '!'
  (id, d, st, t) <- parens domStTy
  spaces
  char '.'
  spaces
  SSend id d st t <$> type5

sRecv = tl $ do
  char '?'
  (id, d, st, t) <- parens domStTy
  spaces
  char '.'
  spaces
  SRecv id d st t <$> type5

sChoice = tl $ do
  t <- type4
  spaces
  kwChoice
  spaces
  SChoice t <$> type3

sBranch = tl $ do
  t <- type4
  spaces
  char '&'
  spaces
  SBranch t <$> type3

sEnd = tl $ do
  string "End"
  return SEnd

sDual = tl $ do
  char '~'
  SDual <$> type4

shEmpty = tl $ do
  kwShEmpty
  return SHEmpty

shSingle = tl $ do
  kwShSingle
  return SHSingle

shMerge = tl $ do
  t <- type7
  spaces
  SHMerge t <$> type6

dEmpty = tl $ do
  char '*'
  return DEmpty

dMerge = tl $ do
  t <- type7
  spaces
  char ','
  spaces
  DMerge t <$> type6

dProj = tl $ do
  l <- lProj
  spaces
  DProj l <$> type9

ssEmpty = tl $ do
  kwStEmpty
  return SSEmpty

ssBind = tl $ do
  t <- type8
  spaces
  kwBind
  spaces
  SSBind t <$> type8

ssMerge = tl $ do
  t <- type7
  spaces
  char ','
  spaces
  DMerge t <$> type6

type1 = tl $ tLam P.<|> eAll P.<|> type2
type2 = tl $ eTup <|> type3
type3 = tl $ sChoice <|> sBranch <|> type4
type4 = tl $ sDual P.<|> type5
type5 = tl $ sSend P.<|> sRecv P.<|> type6
type6 = tl $ ssMerge <|> dMerge <|> shMerge <|> type7
type7 = tl $ ssBind <|> type8
type8 = tl $ dProj P.<|> eChan P.<|> tApp <|> type9 
type9 = tl (ssEmpty P.<|> dEmpty P.<|> shSingle P.<|> shEmpty P.<|> sEnd P.<|> eUnit P.<|> eAcc P.<|> parens type1 P.<|> tVar) <?> "type"


{- expressions & values -}

let1 = tl $ do
  string "let"
  space1
  var <- identifier
  spaces
  char '='
  spaces
  exp <- expr1
  space1
  string "in"
  space1
  Let var exp <$> expr1

app = tl $ do
  v <- val2
  space1
  App v <$> val1

proj = tl $ do
  l <- lProj
  space1
  Proj l <$> val1

aapp = tl $ do
  v <- val2
  spaces
  t <- brackets type1
  return (AApp v t)

fork = tl $ do
  string "fork"
  space1
  Fork <$> val1

acc = tl $ do
  string "accept"
  space1
  Acc <$> val1

req = tl $ do
  string "request"
  space1
  Req <$> val1

send = tl $ do
  string "send"
  space1
  v <- val1
  space1
  string "on"
  space1
  Send v <$> val1

recv = tl $ do
  string "receive"
  space1
  Recv <$> val1

sel = tl $ do
  string "select"
  space1
  v <- label
  space
  spaces
  string "on"
  space1
  Sel v <$> val1

case_ = tl $ do
  string "case"
  space1
  v <- val1
  space
  spaces
  string "of"
  space1
  (e, e_) <- braces (do
    e <- expr1
    spaces
    char ';'
    spaces
    e_ <- expr1
    return (e, e_))
  return (Case v e e_)

close = tl $ do
  string "close"
  space1
  Close <$> val1

new = tl $ do
  string "new"
  space1
  New <$> type1

val = tl $ Val <$> val1

vVar = tl $ VVar <$> identifier

vChan = tl $ do
  string "chan"
  space1
  VChan . TVar <$> identifier

stBindTy = tl $ do
  st <- braces type1
  spaces
  char ';'
  spaces
  id <- identifier
  spaces
  char ':'
  spaces
  t <- type1
  return (st, id, t)

vAbs = tl $ do
  kwLambda
  spaces
  (st, id, t) <- parens stBindTy
  spaces
  char '.'
  spaces
  VAbs st id t <$> expr1

vTAbs = tl $ do
  kwTLambda
  (id, k) <- parens kBind
  spaces
  char '.'
  spaces
  cs <- option [] (do
    cs <- parens cstrs
    spaces
    kwCstrArr
    return cs)
  spaces
  VTAbs id k cs <$> val1

vUnit = tl $ do
  string "unit"
  return VUnit

vPair = tl $ parens $ do
  v <- val1
  spaces
  char ','
  spaces
  VPair v <$> val1

expr1 = tl $ let1 P.<|> expr2 
expr2 = tl $ app <|> expr3
expr3 = tl (fork P.<|> acc P.<|> req P.<|> send P.<|> recv P.<|> sel P.<|> case_ P.<|> close P.<|> new <|> val <|> parens expr1) <?> "expr" 

val1 = tl $ vAbs P.<|> vTAbs P.<|> val2
val2 = tl (vChan <|> vUnit <|> vPair <|> parens val1 <|> vVar) <?> "val" 