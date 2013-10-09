module Popl14.Change.Derive where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Change.Type
open import Popl14.Change.Term

open import Data.Integer

import Parametric.Change.Derive Const ΔBase as Derive

deriveConst : Derive.Structure
deriveConst (intlit-const n) ∅ ∅ = intlit (+ 0)
deriveConst add-const        (s • t • ∅) (ds • dt • ∅) = add ds dt
deriveConst minus-const      (t • ∅) (dt • ∅) = minus dt
deriveConst empty-const      ∅ ∅ = empty
deriveConst insert-const     (s • t • ∅) (ds • dt • ∅) = insert (s ⊕₍ int ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ insert s t
deriveConst union-const      (s • t • ∅) (ds • dt • ∅) = union ds dt
deriveConst negate-const     (t • ∅) (dt • ∅) = negate dt
deriveConst flatmap-const    (s • t • ∅) (ds • dt • ∅) = flatmap (s ⊕₍ int ⇒ bag ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ flatmap s t
deriveConst sum-const        (t • ∅) (dt • ∅) = sum dt

open Derive.Structure deriveConst public
