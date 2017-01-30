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
    ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base nil-base ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
  as ChangeEvaluation

private
  {-# TERMINATING #-}
  meaning-⊕-base : ChangeEvaluation.ApplyStructure
  meaning-⊝-base : ChangeEvaluation.DiffStructure
  meaning-onil-base : ChangeEvaluation.NilStructure

meaning-structure : ChangeEvaluation.Structure
meaning-structure = record
  { meaning-⊕-base = meaning-⊕-base
  ; meaning-⊝-base = meaning-⊝-base
  ; meaning-onil-base = meaning-onil-base
  }

module R = ChangeEvaluation.Structure meaning-structure

meaning-⊕-base base-int = refl
meaning-⊕-base base-bag = refl

meaning-⊝-base base-int = refl
meaning-⊝-base base-bag = refl

meaning-onil-base base-int = refl
meaning-onil-base base-bag = refl

open R public
