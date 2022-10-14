{-# LANGUAGE FlexibleInstances #-}
module Pretty where 

import Ast

class Pretty a where
  pp :: Int -> a -> String
  pretty :: a -> String 
  pretty = pp 0

instance Pretty a => Pretty [a] where
  pp p [] = ""
  pp p [x] = pp p x
  pp p (x : xs) = pp p x ++ ", " ++ pp p xs

brace p1 p2 s = if p1 > p2 then "(" ++ s ++ ")" else s

instance Pretty Kind where 
  pp p KType = "Type"
  pp p KSession = "Session"
  pp p KState = "State"
  pp p KShape = "Shape"
  pp p (KDom t) = "Dom " ++ pp 0 t
  pp p (KLam k k') = brace p 5 (pp 6 k ++ " → " ++ pp 5 k')

instance Pretty Cstr where
  pp p (t, t') = pp 0 t ++ " # " ++ pp 0 t'

instance Pretty (Ctx, Type, Type) where
  pp p (ctx, st, t) = "∃" ++ pp 0 ctx ++ ". " ++ pp 0 st ++  "; " ++ pp 0 t

instance Pretty Program where
  pp p (abs, cbs, es) = "[" ++ pp 0 abs ++ "]\n[" ++ pp 0 cbs ++ "]\n[" ++ pp 0 es ++ "]"

instance Pretty (String, Type) where
  pp p (s, t) = "ν" ++ s ++ " : " ++ pp 0 t

instance Pretty ((String, String), Type) where
  pp p ((s, s'), t) = "ν" ++ s ++ "," ++ s' ++ " ↦ " ++ pp 0 t

instance Pretty (String, Has) where
  pp p (s, HasType t) = s ++ " : " ++ pp p t
  pp p (s, HasKind k) = s ++ " : " ++ pp p k
  pp p (s, HasCstr c) = s ++ " : " ++ pp p c

instance Pretty Label where
  pp p LLeft = "₁"
  pp p LRight = "₂"

prettyLabel LLeft = "1"
prettyLabel LRight  = "2"

instance Pretty Type where   
  pp p (TVar s) = s
  pp p (TApp ty ty') = brace p 100 (pp 100 ty ++ " " ++ pp 101 ty')
  pp p (TLam s k ty) = brace p 5 ("λ(" ++ s ++ " : " ++ pp 0 k ++ "). " ++ pp 5 ty)
  pp p (EAll s ki [] ty) = brace p 5 ("∀(" ++ s ++ " : " ++ pp 0 ki ++ "). " ++ pp 5 ty)
  pp p (EAll s ki xs ty) = brace p 5 ("∀(" ++ s ++ " : " ++ pp 0 ki ++ "). (" ++ pp 0 xs ++ ") => " ++ pp 5 ty)
  pp p (EArr st1 ty1 [] st2 ty2) = brace p (-1) (pp 0 st1 ++ "; " ++ pp 0 ty1 ++ " → " ++ pp 0 st2 ++ "; " ++ pp 0 ty2)
  pp p (EArr st1 ty1 ctx st2 ty2) = brace p (-1) (pp 0 st1 ++ "; " ++ pp 0 ty1 ++ " → " ++ "∃" ++ pp 0 ctx ++ ". " ++ pp 0 st2 ++ "; " ++ pp 0 ty2)

  pp p (EChan ty) = brace p 100 ("Chan " ++ pp 101 ty)
  pp p (EAcc ty) = brace p 100 ("[" ++ pp 0 ty ++ "]")
  pp p EUnit = "Unit"
  pp p (EPair ty ty') = brace p (-1) (pp 0 ty ++ " × " ++ pp 0 ty')
  pp p (SSend s ki st ty ty2) = brace p 100 ("!(∃" ++ s ++ " : " ++ pp 0 ki ++ ". " ++ pp 0 st ++ "). " ++ pp 100 ty2)
  pp p (SRecv s ki st ty ty2) = brace p 100 ("?(∃" ++ s ++ " : " ++ pp 0 ki ++ ". " ++ pp 0 st ++ "). " ++ pp 100 ty2)
  pp p (SChoice ty ty') = brace p 4 (pp 5 ty  ++ " ⊕ " ++ pp 4 ty')
  pp p (SBranch ty ty') = brace p 4 (pp 5 ty  ++ " & " ++ pp 4 ty')
  pp p SEnd = "End"
  pp p (SDual ty) = brace p 80 ("~ " ++ pp 80 ty)
  pp p SHEmpty = "I"
  pp p SHSingle = "X"
  pp p (SHMerge ty ty') = brace p 3 (pp 4 ty ++ " ; " ++ pp 4 ty')
  pp p DEmpty = "∗"
  pp p (DMerge ty ty') = brace p 3 (pp 4 ty ++ " , " ++ pp 4 ty')
  pp p (DProj la ty) = brace p 100 ("𝜋" ++ pp 0 la ++ " " ++ pp 101 ty)
  pp p SSEmpty = "·"
  pp p (SSBind ty ty') = brace p 4 (pp 5 ty ++ " ↦ " ++ pp 5 ty') 
  pp p (SSMerge ty ty') = brace p 3 (pp 3 ty ++ " , " ++ pp 3 ty')

instance Pretty Expr where   
  pp p (Let s ex ex') = brace p 1 ("let " ++ s ++ " = " ++ pp 0 ex ++ " in " ++ pp 1 ex')
  pp p (Val val) = pp p val
  pp p (Proj la val) = brace p 100 ("𝜋" ++ pp 0 la ++ " " ++ pp 101 val)
  pp p (App val val') = brace p 100 (pp 100 val ++ " " ++ pp 101 val')
  pp p (AApp val ty) = brace p 100 (pp 100 val ++ "[" ++ pp 0 ty ++ "]")
  pp p (Fork val) = brace 100 p ("fork " ++ pp 101 val)
  pp p (Acc val) = brace 100 p ("accept " ++ pp 101 val)
  pp p (Req val) = brace 100 p ("request " ++ pp 101 val)
  pp p (Send val val') = brace 100 p ("send " ++ pp 0 val ++ " on " ++ pp 101 val')
  pp p (Recv val) = brace 100 p ("receive " ++ pp 101 val)
  pp p (Sel la val) = brace 100 p ("select " ++ prettyLabel la  ++ " on " ++ pp 101 val)
  pp p (Case val ex ex') = brace 1 p  ("case " ++ pp 0 val ++ " of { " ++ pp 0 ex ++ "; " ++ pp 0 ex' ++ " }")
  pp p (Close val) = brace 100 p ("close " ++ pp 101 val)
  pp p (New ty) = brace 100 p ("new " ++ pp 101 ty)

instance Pretty Val where
  pp p (VVar s) = s
  pp p VUnit = "unit"
  pp p (VPair val val') = brace p (-1) (pp 0 val ++ " , " ++ pp 0 val')
  pp p (VTAbs s ki [] val) = brace p 1 ("Λ(" ++ s ++ " : " ++ pp 0 ki ++ "). " ++ pp 1 val)
  pp p (VTAbs s ki xs val) = brace p 1 ("Λ(" ++ s ++ " : " ++ pp 0 ki ++ "). (" ++ pp 0 xs ++ ") => " ++ pp 1 val)
  pp p (VChan ty) = brace p 100 ("chan " ++ pp 101 ty)
  pp p (VAbs ty s ty' ex) = brace p 1 ("λ(" ++ pp 0 ty ++ "; " ++ s ++ " : " ++ pp 0 ty' ++ "). " ++ pp 1 ex)
