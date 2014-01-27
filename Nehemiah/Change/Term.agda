module Nehemiah.Change.Term where

-- Terms Calculus Nehemiah
--
-- Contents
-- - Term constructors
-- - Weakening on terms
-- - `fit`: weaken a term to its ΔContext
-- - diff-term, apply-term and their syntactic sugars

open import Data.Integer

open import Nehemiah.Syntax.Type public
open import Nehemiah.Syntax.Term public
open import Nehemiah.Change.Type public

import Parametric.Change.Term Const ΔBase as ChangeTerm

diff-base : ChangeTerm.DiffStructure
diff-base {base-int} = abs₂ (λ x y → add x (minus y))
diff-base {base-bag} = abs₂ (λ x y → union x (negate y))

apply-base : ChangeTerm.ApplyStructure
apply-base {base-int} = abs₂ (λ Δx x → add x Δx)
apply-base {base-bag} = abs₂ (λ Δx x → union x Δx)

open ChangeTerm.Structure diff-base apply-base public
