------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Standard evaluation for MTerm
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value

import Parametric.Syntax.MType as MType
import Parametric.Syntax.MTerm as MTerm
import Parametric.Denotation.MValue as MValue


module Parametric.Denotation.MEvaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (ValConst : MTerm.ValConstStructure Const)
    (CompConst : MTerm.CompConstStructure Const)
  where

open Type.Structure Base

open MType.Structure Base
open MTerm.Structure Const ValConst CompConst
open MValue.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation

-- Extension Point: Evaluation of fully applied constants.
ValStructure : Set
ValStructure = ∀ {Σ τ} → ValConst Σ τ → ⟦ Σ ⟧ → ⟦ τ ⟧

CompStructure : Set
CompStructure = ∀ {Σ τ} → CompConst Σ τ → ⟦ Σ ⟧ → ⟦ τ ⟧

module Structure
       (⟦_⟧ValBase  : ValStructure)
       (⟦_⟧CompBase : CompStructure)
    where

  -- We provide: Evaluation of arbitrary value/computation terms.
  ⟦_⟧Comp : ∀ {τ Γ} → Comp Γ τ → ⟦ Γ ⟧ValContext → ⟦ τ ⟧CompType
  ⟦_⟧Val : ∀ {τ Γ} → Val Γ τ → ⟦ Γ ⟧ValContext → ⟦ τ ⟧ValType
  ⟦_⟧Vals : ∀ {Γ Σ} → Vals Γ Σ → ⟦ Γ ⟧ → ⟦ Σ ⟧

  ⟦ ∅ ⟧Vals ρ = ∅
  -- XXX I don't use this enough, but Val should be ValTerms or ValTms (since
  -- we're talking about terms representing values, not values themselves). Or
  -- maybe these are syntactic values... (but not really, variables are
  -- allowed!)
  ⟦ vt • valtms ⟧Vals ρ = ⟦ vt ⟧Val ρ • ⟦ valtms ⟧Vals ρ

  ⟦ vVar x        ⟧Val ρ = ⟦ x ⟧ValVar ρ
  ⟦ vThunk x      ⟧Val ρ = ⟦ x ⟧Comp ρ
  ⟦ vConst c args ⟧Val ρ = ⟦ c ⟧ValBase (⟦ args ⟧Vals ρ)

  ⟦ cConst c args ⟧Comp ρ = ⟦ c ⟧CompBase (⟦ args ⟧Vals ρ)
  ⟦ cForce x      ⟧Comp ρ = ⟦ x ⟧Val ρ
  ⟦ cReturn v     ⟧Comp ρ = ⟦ v ⟧Val ρ
  ⟦ cAbs c        ⟧Comp ρ = λ x → ⟦ c ⟧Comp (x • ρ)
  ⟦ cApp s t      ⟧Comp ρ = ⟦ s ⟧Comp ρ (⟦ t ⟧Val ρ)
  ⟦ c₁ into c₂     ⟧Comp ρ = ⟦ c₂ ⟧Comp (⟦ c₁ ⟧Comp ρ • ρ)

  meaningOfVal : ∀ {Γ τ} → Meaning (Val Γ τ)
  meaningOfVal = meaning ⟦_⟧Val

  -- Evaluation.agda also proves weaken-sound.
