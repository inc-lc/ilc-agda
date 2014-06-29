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

apply-base : ChangeTerm.ApplyStructure
apply-base {base-int} = absV 2 (λ Δx x → add x Δx)
apply-base {base-bag} = absV 2 (λ Δx x → union x Δx)

diff-base : ChangeTerm.DiffStructure
diff-base {base-int} = absV 2 (λ x y → add x (minus y))
diff-base {base-bag} = absV 2 (λ x y → union x (negate y))

nil-base : ChangeTerm.NilStructure
nil-base {base-int} = absV 1 (λ x → intlit (+ 0))
nil-base {base-bag} = absV 1 (λ x → empty)

open ChangeTerm.Structure apply-base diff-base nil-base public
