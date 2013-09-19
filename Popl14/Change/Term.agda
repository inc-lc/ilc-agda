module Popl14.Change.Term where

-- Terms Calculus Popl14
--
-- Contents
-- - Term constructors
-- - Weakening on terms
-- - `fit`: weaken a term to its ΔContext
-- - diff-term, apply-term and their syntactic sugars

open import Data.Integer

open import Popl14.Syntax.Type public
open import Popl14.Syntax.Term public
open import Popl14.Change.Type public

import Parametric.Change.Term Const ΔBase as ChangeTerm

diff-base : ChangeTerm.DiffStructure
diff-base {base-int} = abs₂ (λ x y → add x (minus y))
diff-base {base-bag} = abs₂ (λ x y → union x (negate y))

apply-base : ChangeTerm.ApplyStructure
apply-base {base-int} = abs₂ (λ Δx x → add x Δx)
apply-base {base-bag} = abs₂ (λ Δx x → union x Δx)

open ChangeTerm.Structure diff-base apply-base public
