------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Terms that operate on changes with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Term where

open import Data.Integer

open import Nehemiah.Syntax.Type public
open import Nehemiah.Syntax.Term public
open import Nehemiah.Change.Type public

import Parametric.Change.Term Const ΔBase as ChangeTerm

{-# TERMINATING #-}
apply-base : ChangeTerm.ApplyStructure
diff-base : ChangeTerm.DiffStructure
nil-base : ChangeTerm.NilStructure

open ChangeTerm.Structure apply-base diff-base nil-base public

apply-base {base-int} = absV 2 (λ Δx x → add x Δx)
apply-base {base-bag} = absV 2 (λ Δx x → union x Δx)
apply-base {base-pair τ₁ τ₂} = absV 2 (λ Δx x → pair (apply τ₁ (fst Δx) (fst x)) (apply τ₂ (snd Δx) (snd x)))

diff-base {base-int} = absV 2 (λ x y → add x (minus y))
diff-base {base-bag} = absV 2 (λ x y → union x (negate y))
diff-base {base-pair τ₁ τ₂} = absV 2 (λ x y → pair (diff τ₁ (fst x) (fst y)) (diff τ₂ (snd x) (snd y)))

open import Data.Product
nil-base {base-int} = absV 1 (λ x → intlit (+ 0))
nil-base {base-bag} = absV 1 (λ x → empty)
nil-base {base-pair τ₁ τ₂} = absV 1 (λ x → pair (onil (fst x)) (onil (snd x)))
