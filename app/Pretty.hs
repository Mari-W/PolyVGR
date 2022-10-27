{-# LANGUAGE FlexibleInstances #-}
module Pretty where

import Ast
    ( Cstr,
      Ctx,
      Expr(..),
      Has(..),
      Kind(..),
      Label(..),
      Program,
      Type(..),
      Val(..) )

class Pretty a where
  pp :: Int -> Int -> a -> String
  pretty :: a -> String
  pretty = pp 0 0

instance Pretty a => Pretty [a] where
  pp i p [] = ""
  pp i p [x] = pp i p x
  pp i p (x : xs) = pp i p x ++ ", " ++ pp i p xs

brace p1 p2 s = if p1 > p2 then "(" ++ s ++ ")" else s
indent i s = concat (replicate i "  ") ++ s

instance Pretty Kind where
  pp i p KType = "Type"
  pp i p KSession = "Session"
  pp i p KState = "State"
  pp i p KShape = "Shape"
  pp i p (KDom t) = "Dom " ++ pp i 0 t
  pp i p (KArr k k') = brace p 5 (pp i 6 k ++ " → " ++ pp i 5 k')

instance Pretty Cstr where
  pp i p (t, t') = pp i 0 t ++ " # " ++ pp i 0 t'

instance Pretty (Ctx, Type, Type) where
  pp i p ([], st, t) = pp i 0 st ++  "; " ++ pp i 0 t
  pp i p (ctx, st, t) = "∃" ++ pp i 0 ctx ++ ". " ++ pp i 0 st ++  "; " ++ pp i 0 t

instance Pretty Program where
  pp i p (abs, cbs, es) = printIf abs ("Access Points:\n" ++ concatMap (\a -> pp i 0 a ++ "\n") abs) ++ 
                          printIf cbs ("\nChannels:\n" ++ concatMap (\c -> pp i 0 c ++ "\n") cbs) ++ 
                          printIf es ("\nThreads:\n" ++ concatMap (\(j, a) -> "---- [" ++ show (j + 1) ++ "] ----\n" 
                                      ++  pp i 0 a ++ "\n") (enumerate es))
                          where enumerate = zip [0..]
                                printIf l s = if null l then "" else s 

instance Pretty (String, Type) where
  pp i p (s, t) = "𝜈" ++ s ++ " : " ++ pp i 0 t

instance Pretty ((String, String), Type) where
  pp i p ((s, s'), t) = "𝜈" ++ s ++ "," ++ s' ++ " ↦ " ++ pp i 0 t

instance Pretty (String, Has) where
  pp i p (s, HasType t) = s ++ " : " ++ pp i p t
  pp i p (s, HasKind k) = s ++ " : " ++ pp i p k
  pp i p (s, HasCstr c) = pp i p c

instance Pretty Label where
  pp i p LLeft = "₁"
  pp i p LRight = "₂"

prettyLabel LLeft = "1"
prettyLabel LRight  = "2"

instance Pretty Type where
  pp i p (TVar s) = s
  pp i p (TApp ty ty') = brace p 100 (pp i 100 ty ++ " " ++ pp i 101 ty')
  pp i p (TLam s k ty) = brace p 5 ("λ(" ++ s ++ " : " ++ pp i 0 k ++ "). " ++ pp i 5 ty)
  pp i p (EAll s ki [] ty) = brace p 5 ("∀(" ++ s ++ " : " ++ pp i 0 ki ++ "). " ++ pp i 5 ty)
  pp i p (EAll s ki xs ty) = brace p 5 ("∀(" ++ s ++ " : " ++ pp i 0 ki ++ "). (" 
                                                   ++ pp i 0 xs ++ ") => " ++ pp i 5 ty)
  pp i p (EArr st1 ty1 [] st2 ty2) = brace p (-1) (pp i 0 st1 ++ "; " ++ pp i 0 ty1 ++ " → " 
                                                              ++ pp i 0 st2 ++ "; " ++ pp i 0 ty2)
  pp i p (EArr st1 ty1 ctx st2 ty2) = brace p (-1) (pp i 0 st1 ++ "; " ++ pp i 0 ty1 ++ " → " ++ "∃" 
                                                               ++ pp i 0 ctx ++ ". " ++ pp i 0 st2 ++ "; " 
                                                               ++ pp i 0 ty2)
  pp i p (EChan ty) = brace p 100 ("Chan " ++ pp i 101 ty)
  pp i p (EAcc ty) = brace p 100 ("[" ++ pp i 0 ty ++ "]")
  pp i p EUnit = "Unit"
  pp i p EInt = "Int"
  pp i p (EPair ty ty') = brace p (-1) (pp i 0 ty ++ " × " ++ pp i 0 ty')
  pp i p (SSend s ki st ty ty2) = brace p 100 ("!(∃" ++ s ++ " : " ++ pp i 0 ki ++ ". " ++ pp i 0 st 
                                                          ++ "). " ++ pp i 100 ty2)
  pp i p (SRecv s ki st ty ty2) = brace p 100 ("?(∃" ++ s ++ " : " ++ pp i 0 ki ++ ". " ++ pp i 0 st 
                                                          ++ "). " ++ pp i 100 ty2)
  pp i p (SChoice ty ty') = brace p 4 (pp i 5 ty  ++ " ⊕ " ++ pp i 4 ty')
  pp i p (SBranch ty ty') = brace p 4 (pp i 5 ty  ++ " & " ++ pp i 4 ty')
  pp i p SEnd = "End"
  pp i p (SDual ty) = brace p 80 ("~ " ++ pp i 80 ty)
  pp i p SHEmpty = "𝕀"
  pp i p SHSingle = "𝕏"
  pp i p (SHMerge ty ty') = brace p (-1) (pp i 4 ty ++ " ; " ++ pp i 4 ty')
  pp i p DEmpty = "∗"
  pp i p (DMerge ty ty') = brace p 3 (pp i 4 ty ++ " , " ++ pp i 4 ty')
  pp i p (DProj la ty) = brace p 100 ("π" ++ pp i 0 la ++ " " ++ pp i 101 ty)
  pp i p SSEmpty = "·"
  pp i p (SSBind ty ty') = brace p 4 (pp i 5 ty ++ " ↦ " ++ pp i 5 ty')
  pp i p (SSMerge SSEmpty SSEmpty) = brace p 3 "·"
  pp i p (SSMerge SSEmpty ty') = brace p 3 (pp i 3 ty')
  pp i p (SSMerge ty SSEmpty) = brace p 3 (pp i 3 ty)
  pp i p (SSMerge ty ty') = brace p 3 (pp i 3 ty ++ " , " ++ pp i 3 ty')

instance Pretty Expr where
  pp i p (Let s ex ex') = brace p 1 ("let " ++ s ++ " = " ++ pp (i + 1) 0 ex ++ " in\n" ++ indent i (pp i 1 ex'))
  pp i p (Val val) = pp i p val
  pp i p (Proj la val) = brace p 100 ("𝜋" ++ pp i 0 la ++ " " ++ pp i 101 val)
  pp i p (App val val') = brace p 100 (pp i 100 val ++ " " ++ pp i 101 val')
  pp i p (AApp val ty) = brace p 100 (pp i 100 val ++ " [" ++ pp i 0 ty ++ "]")
  pp i p (Fork val) = brace p 100  ("fork " ++ pp i 101 val)
  pp i p (Acc val) = brace p 100 ("accept " ++ pp i 101 val)
  pp i p (Req val) = brace p 100 ("request " ++ pp i 101 val)
  pp i p (Send val val') = brace p 100 ("send " ++ pp i 0 val ++ " on " ++ pp i 101 val')
  pp i p (Recv val) = brace p 100 ("receive " ++ pp i 101 val)
  pp i p (Sel la val) = brace p 100 ("select " ++ prettyLabel la  ++ " on " ++ pp i 101 val)
  pp i p (Case val ex ex') = brace p 1 ("case " ++ pp i 0 val ++ " of { " ++ pp i 0 ex ++ "; " 
                                                   ++ pp i 0 ex' ++ " }")
  pp i p (Close val) = brace p 100 ("close " ++ pp i 101 val)
  pp i p (New ty) = brace p 100  ("new " ++ pp i 101 ty)

instance Pretty Val where
  pp i p (VVar s) = s
  pp i p VUnit = "unit"
  pp i p (VInt j) = show j
  pp i p (VPair val val') = brace p (-1) (pp i 0 val ++ " , " ++ pp i 0 val')
  pp i p (VTAbs s ki [] val) = brace p 1 ("Λ(" ++ s ++ " : " ++ pp i 0 ki ++ ").\n" ++ indent i (pp i 1 val))
  pp i p (VTAbs s ki xs val) = brace p 1 ("Λ(" ++ s ++ " : " ++ pp i 0 ki ++ "). (" ++ pp i 0 xs 
                                                     ++ ") =>\n" ++ indent i (pp i 1 val))
  pp i p (VChan ty) = brace p 100 ("chan " ++ pp i 101 ty)
  pp i p (VAbs ty s ty' ex) = brace p 1 ("λ(" ++ pp i 0 ty ++ "; " ++ s ++ " : " ++ pp i 0 ty' 
                                                    ++ ").\n" ++ indent i (pp i 1 ex))
