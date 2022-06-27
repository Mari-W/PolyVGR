module KindFormation where

import Ast (Ctx, Has (HasDisCon, HasKind, HasType), Kind (KDom, KLam))
import GHC.Generics (K1 (K1))
import Result (Result, ok, raise)
import TypeFormation (shapeWellFormed)

kindWellFormed :: Ctx -> Kind -> Result ()
kindWellFormed ctx (KDom shape) = shapeWellFormed ctx shape
kindWellFormed ctx (KLam k1 k2) = do
  kindWellFormed ctx k1
  kindWellFormed ctx k2
kindWellFormed _ _ = ok ()