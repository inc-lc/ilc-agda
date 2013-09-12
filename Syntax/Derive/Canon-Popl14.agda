module Syntax.Derive.Canon-Popl14 where

open import Syntax.Term.Popl14 public
open import Popl14.Syntax.Type
open import Syntax.Language.Popl14

open import Data.Integer

import Parametric.Change.Derive Const ΔBase as Derive

deriveConst : Derive.Structure
deriveConst (intlit-c n) ∅ = intlit (+ 0)
deriveConst add-c        (ds • s • dt • t • ∅) = add ds dt
deriveConst minus-c      (dt • t • ∅) = minus dt
deriveConst empty-c      ∅ = empty
deriveConst insert-c     (ds • s • dt • t • ∅) = insert (s ⊕ ds) (t ⊕ dt) ⊝ insert s t
deriveConst union-c      (ds • s • dt • t • ∅) = union ds dt
deriveConst negate-c     (dt • t • ∅) = negate dt
deriveConst flatmap-c    (ds • s • dt • t • ∅) = flatmap (s ⊕ ds) (t ⊕ dt) ⊝ flatmap s t
deriveConst sum-c        (dt • t • ∅) = sum dt

open Derive.Structure deriveConst public
