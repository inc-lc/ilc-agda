module Popl14.Change.Derive where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Change.Type
open import Popl14.Change.Term

open import Data.Integer

import Parametric.Change.Derive Const ΔBase as Derive

deriveConst : Derive.Structure
deriveConst (intlit-const n) ∅ = intlit (+ 0)
deriveConst add-const        (ds • s • dt • t • ∅) = add ds dt
deriveConst minus-const      (dt • t • ∅) = minus dt
deriveConst empty-const      ∅ = empty
deriveConst insert-const     (ds • s • dt • t • ∅) = insert (apply {int} ds s) (apply {bag} dt t) ⊝ insert s t
deriveConst union-const      (ds • s • dt • t • ∅) = union ds dt
deriveConst negate-const     (dt • t • ∅) = negate dt
deriveConst flatmap-const    (ds • s • dt • t • ∅) = flatmap (apply {int ⇒ bag} ds s) (apply {bag} dt t) ⊝ flatmap s t
deriveConst sum-const        (dt • t • ∅) = sum dt

open Derive.Structure deriveConst public
