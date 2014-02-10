------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Connecting Nehemiah.Change.Term and Nehemiah.Change.Value.
------------------------------------------------------------------------

module Nehemiah.Change.Evaluation where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term
open import Nehemiah.Change.Value
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation

open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation

import Parametric.Change.Evaluation
    ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base ⟦apply-base⟧ ⟦diff-base⟧
  as ChangeEvaluation

meaning-⊕-base : ChangeEvaluation.ApplyStructure
meaning-⊕-base base-int = refl
meaning-⊕-base base-bag = refl

meaning-⊝-base : ChangeEvaluation.DiffStructure
meaning-⊝-base base-int = refl
meaning-⊝-base base-bag = refl

open ChangeEvaluation.Structure meaning-⊕-base meaning-⊝-base public
