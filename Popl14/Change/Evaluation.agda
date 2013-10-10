module Popl14.Change.Evaluation where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Change.Type
open import Popl14.Change.Term
open import Popl14.Change.Value
open import Popl14.Denotation.Value
open import Popl14.Denotation.Evaluation

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
