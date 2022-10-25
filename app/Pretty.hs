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
  pp i p (x : xs) = pp i p x ++ ", " ++ pp 0 p xs

brace p1 p2 s = if p1 > p2 then "(" ++ s ++ ")" else s
indent i s = concat (replicate i "  ") ++ s

instance Pretty Kind where
  pp i p KType = indent i "Type"
  pp i p KSession = indent i "Session"
  pp i p KState = indent i "State"
  pp i p KShape = indent i "Shape"
  pp i p (KDom t) = indent i "Dom " ++ pp 0 0 t
  pp i p (KArr k k') = indent i $ brace p 5 (pp 0 6 k ++ " → " ++ pp 0 5 k')

instance Pretty Cstr where
  pp i p (t, t') = indent i $ pp 0 0 t ++ " # " ++ pp 0 0 t'

instance Pretty (Ctx, Type, Type) where
  pp i p ([], st, t) = indent i $ pp 0 0 st ++  "; " ++ pp 0 0 t
  pp i p (ctx, st, t) = indent i $ "∃" ++ pp 0 0 ctx ++ ". " ++ pp 0 0 st ++  "; " ++ pp 0 0 t

enumerate = zip [0..]

instance Pretty Program where
  pp i p (abs, cbs, es) = (if null abs then "" else "Access Points:\n" ++ concatMap (\a -> pp 0 0 a ++ "\n") abs) ++ 
                          (if null cbs then "" else "\nChannels:\n" ++ concatMap (\c -> pp 0 0 c ++ "\n") cbs) ++ 
                          (if null es then "" else  "\nThreads:\n" ++ concatMap (\(i, a) -> "----  [" ++ show (i + 1) ++ "] ----\n" ++  pp 0 0 a ++ "\n") (enumerate es))

instance Pretty (String, Type) where
  pp i p (s, t) = indent i $ "𝜈" ++ s ++ " : " ++ pp 0 0 t

instance Pretty ((String, String), Type) where
  pp i p ((s, s'), t) = indent i $ "𝜈" ++ s ++ "," ++ s' ++ " ↦ " ++ pp 0 0 t

instance Pretty (String, Has) where
  pp i p (s, HasType t) = indent i $ s ++ " : " ++ pp 0 p t
  pp i p (s, HasKind k) = indent i $ s ++ " : " ++ pp 0 p k
  pp i p (s, HasCstr c) = indent i $ pp 0 p c

instance Pretty Label where
  pp i p LLeft = indent i "₁"
  pp i p LRight = indent i "₂"

prettyLabel LLeft = "1"
prettyLabel LRight  = "2"

instance Pretty Type where
  pp i p (TVar s) = indent i s
  pp i p (TApp ty ty') = indent i $ brace p 100 (pp i 100 ty ++ " " ++ pp i 101 ty')
  pp i p (TLam s k ty) = indent i $ brace p 5 ("λ(" ++ s ++ " : " ++ pp 0 0 k ++ "). " ++ pp 0 5 ty)
  pp i p (EAll s ki [] ty) = indent i $ brace p 5 ("∀(" ++ s ++ " : " ++ pp 0 0 ki ++ "). " ++ pp 0 5 ty)
  pp i p (EAll s ki xs ty) = indent i $ brace p 5 ("∀(" ++ s ++ " : " ++ pp 0 0 ki ++ "). (" ++ pp 0 0 xs ++ ") => " ++ pp 0 5 ty)
  pp i p (EArr st1 ty1 [] st2 ty2) = indent i $ brace p (-1) (pp 0 0 st1 ++ "; " ++ pp 0 0 ty1 ++ " → " ++ pp 0 0 st2 ++ "; " ++ pp 0 0 ty2)
  pp i p (EArr st1 ty1 ctx st2 ty2) = indent i $ brace p (-1) (pp 0 0 st1 ++ "; " ++ pp 0 0 ty1 ++ " → " ++ "∃" ++ pp 0 0 ctx ++ ". " ++ pp 0 0 st2 ++ "; " ++ pp 0 0 ty2)
  pp i p (EChan ty) = indent i $ brace p 100 ("Chan " ++ pp 0 101 ty)
  pp i p (EAcc ty) = indent i $ brace p 100 ("[" ++ pp 0 0 ty ++ "]")
  pp i p EUnit = indent i "Unit"
  pp i p EInt = indent i "Int"
  pp i p (EPair ty ty') = indent i $ brace p (-1) (pp 0 0 ty ++ " × " ++ pp 0 0 ty')
  pp i p (SSend s ki st ty ty2) = indent i $ brace p 100 ("!(∃" ++ s ++ " : " ++ pp 0 0 ki ++ ". " ++ pp 0 0 st ++ "). " ++ pp 0 100 ty2)
  pp i p (SRecv s ki st ty ty2) = indent i $ brace p 100 ("?(∃" ++ s ++ " : " ++ pp 0 0 ki ++ ". " ++ pp 0 0 st ++ "). " ++ pp 0 100 ty2)
  pp i p (SChoice ty ty') = indent i $ brace p 4 (pp 0 5 ty  ++ " ⊕ " ++ pp 0 4 ty')
  pp i p (SBranch ty ty') = indent i $ brace p 4 (pp 0 5 ty  ++ " & " ++ pp 0 4 ty')
  pp i p SEnd = indent i "End"
  pp i p (SDual ty) = indent i $ brace p 80 ("~ " ++ pp 0 80 ty)
  pp i p SHEmpty = indent i "𝕀"
  pp i p SHSingle = indent i "𝕏"
  pp i p (SHMerge ty ty') = indent i $ brace p (-1) (pp 0 4 ty ++ " ; " ++ pp 0 4 ty')
  pp i p DEmpty = "∗"
  pp i p (DMerge ty ty') = indent i $ brace p 3 (pp 0 4 ty ++ " , " ++ pp 0 4 ty')
  pp i p (DProj la ty) = indent i $ brace p 100 ("π" ++ pp 0 0 la ++ " " ++ pp 0 101 ty)
  pp i p SSEmpty = "·"
  pp i p (SSBind ty ty') = indent i $ brace p 4 (pp 0 5 ty ++ " ↦ " ++ pp 0 5 ty')
  pp i p (SSMerge SSEmpty SSEmpty ) = indent i $ brace p 3 "{}"
  pp i p (SSMerge SSEmpty ty') = indent i $ brace p 3 (pp 0 3 ty')
  pp i p (SSMerge ty SSEmpty) = indent i $ brace p 3 (pp 0 3 ty)
  pp i p (SSMerge ty ty') = indent i $ brace p 3 (pp 0 3 ty ++ " , " ++ pp 0 3 ty')

instance Pretty Expr where
  pp i p (Let s ex ex') = indent i $ brace p 1 ("let " ++ s ++ " = " ++ pp 0 0 ex ++ " in\n" ++ pp i 1 ex')
  pp i p (Val val) = indent i $ pp 0 p val
  pp i p (Proj la val) = indent i $ brace p 100 ("𝜋" ++ pp 0 0 la ++ " " ++ pp 0 101 val)
  pp i p (App val val') = indent i $ brace p 100 (pp 0 100 val ++ " " ++ pp 0 101 val')
  pp i p (AApp val ty) = indent i $ brace p 100 (pp 0 100 val ++ " [" ++ pp 0 0 ty ++ "]")
  pp i p (Fork val) = indent i $ brace p 100  ("fork " ++ pp 0 101 val)
  pp i p (Acc val) = indent i $ brace p 100 ("accept " ++ pp 0 101 val)
  pp i p (Req val) = indent i $ brace p 100 ("request " ++ pp 0 101 val)
  pp i p (Send val val') = indent i $ brace p 100 ("send " ++ pp 0 0 val ++ " on " ++ pp 0 101 val')
  pp i p (Recv val) = indent i $ brace p 100 ("receive " ++ pp 0 101 val)
  pp i p (Sel la val) = indent i $ brace p 100 ("select " ++ prettyLabel la  ++ " on " ++ pp 0 101 val)
  pp i p (Case val ex ex') = indent i $ brace p 1 ("case " ++ pp 0 0 val ++ " of { " ++ pp 0 0 ex ++ "; " ++ pp 0 0 ex' ++ " }")
  pp i p (Close val) = indent i $ brace p 100 ("close " ++ pp 0 101 val)
  pp i p (New ty) = indent i $ brace p 100  ("new " ++ pp 0 101 ty)

instance Pretty Val where
  pp i p (VVar s) = indent i s
  pp i p VUnit = indent i "unit"
  pp i p (VInt j) = indent i (show j)
  pp i p (VPair val val') = indent i $ brace p (-1) (pp 0 0 val ++ " , " ++ pp 0 0 val')
  pp i p (VTAbs s ki [] val) = indent i $ brace p 1 ("Λ(" ++ s ++ " : " ++ pp 0 0 ki ++ ").\n" ++ pp (i+1) 1 val)
  pp i p (VTAbs s ki xs val) = indent i $ brace p 1 ("Λ(" ++ s ++ " : " ++ pp 0 0 ki ++ "). (" ++ pp 0 0 xs ++ ") =>\n" ++ pp (i+1) 1 val)
  pp i p (VChan ty) = indent i $ brace p 100 ("chan " ++ pp 0 101 ty)
  pp i p (VAbs ty s ty' ex) = indent i $ brace p 1 ("λ(" ++ pp 0 0 ty ++ "; " ++ s ++ " : " ++ pp 0 0 ty' ++ ").\n" ++ pp (i+1) 1 ex)
