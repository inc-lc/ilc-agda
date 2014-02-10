------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Standard evaluation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Denotation.Evaluation where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value

open import Data.Integer
open import Structure.Bag.Nehemiah

import Parametric.Denotation.Evaluation Const ⟦_⟧Base as Evaluation

⟦_⟧Const : Evaluation.Structure
⟦ intlit-const n ⟧Const ∅ = n
⟦ add-const ⟧Const (m • n • ∅) = m + n
⟦ minus-const ⟧Const (n • ∅) = - n
⟦ empty-const ⟧Const ∅ = emptyBag
⟦ insert-const ⟧Const (n • b • ∅) = singletonBag n ++ b
⟦ union-const ⟧Const (b₁ • b₂ • ∅) = b₁ ++ b₂
⟦ negate-const ⟧Const (b • ∅) = negateBag b
⟦ flatmap-const ⟧Const (f • b • ∅) = flatmapBag f b
⟦ sum-const ⟧Const (b • ∅) = sumBag b

open Evaluation.Structure ⟦_⟧Const public
