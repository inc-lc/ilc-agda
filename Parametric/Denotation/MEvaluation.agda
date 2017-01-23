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
    (cbnToCompConst : MTerm.CbnToCompConstStructure Const CompConst)
    (cbvToCompConst : MTerm.CbvToCompConstStructure Const CompConst)
  where

open Type.Structure Base

open MType.Structure Base
open MTerm.Structure Const ValConst CompConst cbnToCompConst cbvToCompConst
open MValue.Structure Base ⟦_⟧Base

open import Base.Data.DependentList
open import Base.Denotation.Notation

-- Extension Point: Evaluation of constants.
ValStructure : Set
ValStructure = ∀ {τ} → ValConst τ → ⟦ τ ⟧

CompStructure : Set
CompStructure = ∀ {τ} → CompConst τ → ⟦ τ ⟧

module Structure
       (⟦_⟧ValBase  : ValStructure)
       (⟦_⟧CompBase : CompStructure)
    where

  -- We provide: Evaluation of arbitrary value/computation terms.
  ⟦_⟧Comp : ∀ {τ Γ} → Comp Γ τ → ⟦ Γ ⟧ValContext → ⟦ τ ⟧CompType
  ⟦_⟧Val : ∀ {τ Γ} → Val Γ τ → ⟦ Γ ⟧ValContext → ⟦ τ ⟧ValType

  ⟦ vVar x     ⟧Val ρ  = ⟦ x ⟧ValVar ρ
  ⟦ vThunk x   ⟧Val ρ  = ⟦ x ⟧Comp ρ
  ⟦ vConst c   ⟧Val ρ  = ⟦ c ⟧ValBase

  ⟦ cConst c   ⟧Comp ρ = ⟦ c ⟧CompBase
  ⟦ cForce x   ⟧Comp ρ = ⟦ x ⟧Val ρ
  ⟦ cReturn v  ⟧Comp ρ = ⟦ v ⟧Val ρ
  ⟦ cAbs c     ⟧Comp ρ = λ x → ⟦ c ⟧Comp (x • ρ)
  ⟦ cApp s t   ⟧Comp ρ = ⟦ s ⟧Comp ρ (⟦ t ⟧Val ρ)
  ⟦ c₁ into c₂ ⟧Comp ρ = ⟦ c₂ ⟧Comp (⟦ c₁ ⟧Comp ρ • ρ)

  meaningOfVal : ∀ {Γ τ} → Meaning (Val Γ τ)
  meaningOfVal = meaning ⟦_⟧Val

  -- Evaluation.agda also proves weaken-sound.
