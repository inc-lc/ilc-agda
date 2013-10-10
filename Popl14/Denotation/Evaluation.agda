module Popl14.Denotation.Evaluation where

-- Evaluating terms of Calculus Popl14 into Agda values

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value

open import Data.Integer
open import Structure.Bag.Popl14

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
