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
deriveConst (intlit-const n) = intlit (+ 0)
deriveConst add-const        = absV 4 (λ s ds t dt → add ds dt)
deriveConst minus-const      = absV 2 (λ t dt → minus dt)
deriveConst empty-const      = empty
deriveConst insert-const     = absV 4 (λ s ds t dt →
  insert (s ⊕₍ int ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ insert s t)
deriveConst union-const      = absV 4 (λ s ds t dt → union ds dt)
deriveConst negate-const     = absV 2 (λ t dt → negate dt)
deriveConst flatmap-const    = absV 4 (λ s ds t dt →
  flatmap (s ⊕₍ int ⇒ bag ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ flatmap s t)
deriveConst sum-const        = absV 2 (λ t dt → sum dt)

open Derive.Structure deriveConst public
