module TypeFormation where

import Ast (Ctx, Has (HasKind, HasType, HasDisCon), Shape)
import Result (Result, ok, raise)

shapeWellFormed :: Ctx -> Shape -> Result ()
shapeWellFormed _ _ = ok ()
