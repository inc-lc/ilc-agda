------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Incrementalization as term-to-term transformation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Derive where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term

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
