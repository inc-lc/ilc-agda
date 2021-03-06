module Thesis.LangChanges where

open import Thesis.Changes
open import Thesis.IntChanges
open import Thesis.Types
open import Thesis.Contexts
open import Thesis.Environments
open import Relation.Binary.PropositionalEquality

Chτ : (τ : Type) → Set
Chτ τ = ⟦ Δt τ ⟧Type

ΔΓ : Context → Context
ΔΓ ∅ = ∅
ΔΓ (τ • Γ) = Δt τ • τ • ΔΓ Γ

ChΓ : ∀ (Γ : Context) → Set
ChΓ Γ = ⟦ ΔΓ Γ ⟧Context

[_]τ_from_to_ : ∀ (τ : Type) → (dv : Chτ τ) → (v1 v2 : ⟦ τ ⟧Type) → Set

isCompChangeStructureτ : ∀ τ → IsCompChangeStructure ⟦ τ ⟧Type ⟦ Δt τ ⟧Type [ τ ]τ_from_to_

changeStructureτ : ∀ τ → ChangeStructure ⟦ τ ⟧Type
changeStructureτ τ = record { isCompChangeStructure = isCompChangeStructureτ τ }

instance
  ichangeStructureτ : ∀ {τ} → ChangeStructure ⟦ τ ⟧Type
  ichangeStructureτ {τ} = changeStructureτ τ

[ σ ⇒ τ ]τ df from f1 to f2 =
  ∀ (da : Chτ σ) (a1 a2 : ⟦ σ ⟧Type) →
  [ σ ]τ da from a1 to a2 → [ τ ]τ df a1 da from f1 a1 to f2 a2
[ unit ]τ tt from tt to tt = ⊤
[ int ]τ dv from v1 to v2 = v1 + dv ≡ v2
[ pair σ τ ]τ (da , db) from (a1 , b1) to (a2 , b2) = [ σ ]τ da from a1 to a2 × [ τ ]τ db from b1 to b2
[ sum σ τ ]τ dv from v1 to v2 = sch_from_to_ dv v1 v2

isCompChangeStructureτ (σ ⇒ τ) = ChangeStructure.isCompChangeStructure (funCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ unit = ChangeStructure.isCompChangeStructure unitCS
isCompChangeStructureτ int = ChangeStructure.isCompChangeStructure intCS
isCompChangeStructureτ (pair σ τ) = ChangeStructure.isCompChangeStructure (pairCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ (sum σ τ) = ChangeStructure.isCompChangeStructure (sumCS {{changeStructureτ σ}} {{changeStructureτ τ}})

open import Data.Unit
-- We can define an alternative semantics for contexts, that defines environments as nested products:
⟦_⟧Context-prod : Context → Set
⟦ ∅ ⟧Context-prod = ⊤
⟦ τ • Γ ⟧Context-prod = ⟦ τ ⟧Type × ⟦ Γ ⟧Context-prod

-- And define a change structure for such environments, reusing the change
-- structure constructor for pairs. However, this change structure does not
-- duplicate base values in the environment. We probably *could* define a
-- different change structure for pairs that gives the right result.
changeStructureΓ-old : ∀ Γ → ChangeStructure ⟦ Γ ⟧Context-prod
changeStructureΓ-old ∅ = unitCS
changeStructureΓ-old (τ • Γ) = pairCS {{changeStructureτ τ}}  {{changeStructureΓ-old Γ}}

data [_]Γ_from_to_ : ∀ Γ → ChΓ Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set where
  v∅ : [ ∅ ]Γ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Γ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ]τ dv from v1 to v2) →
    (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
    [ τ • Γ ]Γ (dv • v1 • dρ) from (v1 • ρ1) to (v2 • ρ2)

module _ where
  _e⊕_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΓ Γ → ⟦ Γ ⟧Context
  _e⊕_ ∅ ∅ = ∅
  _e⊕_ (v • ρ) (dv • _ • dρ) = v ⊕ dv • ρ e⊕ dρ
  _e⊝_ : ∀ {Γ} → ⟦ Γ ⟧Context → ⟦ Γ ⟧Context → ChΓ Γ
  _e⊝_ ∅ ∅ = ∅
  _e⊝_ (v₂ • ρ₂) (v₁ • ρ₁) = v₂ ⊝ v₁ • v₁ • ρ₂ e⊝ ρ₁

  isEnvCompCS : ∀ Γ → IsCompChangeStructure ⟦ Γ ⟧Context (ChΓ Γ) [ Γ ]Γ_from_to_

  efromto→⊕ : ∀ {Γ} (dρ : ChΓ Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context) →
      [ Γ ]Γ dρ from ρ1 to ρ2 → (ρ1 e⊕ dρ) ≡ ρ2
  efromto→⊕ .∅ .∅ .∅ v∅ = refl
  efromto→⊕ .(_ • _ • _) .(_ • _) .(_ • _) (dvv v• dρρ) =
    cong₂ _•_ (fromto→⊕ _ _ _ dvv) (efromto→⊕ _ _ _ dρρ)

  e⊝-fromto : ∀ {Γ} → (ρ1 ρ2 : ⟦ Γ ⟧Context) → [ Γ ]Γ ρ2 e⊝ ρ1 from ρ1 to ρ2
  e⊝-fromto ∅ ∅ = v∅
  e⊝-fromto (v1 • ρ1) (v2 • ρ2) = ⊝-fromto v1 v2 v• e⊝-fromto ρ1 ρ2

  _e⊚_ : ∀ {Γ} → ChΓ Γ → ChΓ Γ → ChΓ Γ
  _e⊚_ {∅} ∅ ∅ = ∅
  _e⊚_ {τ • Γ} (dv1 • v1 • dρ1) (dv2 • _ • dρ2) = dv1 ⊚[ ⟦ τ ⟧Type ] dv2 • v1 • dρ1 e⊚ dρ2

  e⊚-fromto : ∀ Γ → (ρ1 ρ2 ρ3 : ⟦ Γ ⟧Context) (dρ1 dρ2 : ChΓ Γ) →
    [ Γ ]Γ dρ1 from ρ1 to ρ2 →
    [ Γ ]Γ dρ2 from ρ2 to ρ3 → [ Γ ]Γ (dρ1 e⊚ dρ2) from ρ1 to ρ3
  e⊚-fromto ∅ ∅ ∅ ∅ ∅ ∅ v∅ v∅ = v∅
  e⊚-fromto (τ • Γ) (v1 • ρ1) (v2 • ρ2) (v3 • ρ3)
    (dv1 • (.v1 • dρ1)) (dv2 • (.v2 • dρ2))
    (dvv1 v• dρρ1) (dvv2 v• dρρ2) =
        ⊚-fromto v1 v2 v3 dv1 dv2 dvv1 dvv2
      v•
        e⊚-fromto Γ ρ1 ρ2 ρ3 dρ1 dρ2 dρρ1 dρρ2

  isEnvCompCS Γ = record
    { isChangeStructure = record
      { _⊕_ = _e⊕_
      ; fromto→⊕ = efromto→⊕
      ; _⊝_ = _e⊝_
      ; ⊝-fromto = e⊝-fromto
      }
    ; _⊚_ = _e⊚_
    ; ⊚-fromto = e⊚-fromto Γ
    }

changeStructureΓ : ∀ Γ → ChangeStructure ⟦ Γ ⟧Context
changeStructureΓ Γ = record { isCompChangeStructure = isEnvCompCS Γ }

instance
  ichangeStructureΓ : ∀ {Γ} → ChangeStructure ⟦ Γ ⟧Context
  ichangeStructureΓ {Γ} = changeStructureΓ Γ

changeStructureΓτ : ∀ Γ τ → ChangeStructure (⟦ Γ ⟧Context → ⟦ τ ⟧Type)
changeStructureΓτ Γ τ = funCS

instance
  ichangeStructureΓτ : ∀ {Γ τ} → ChangeStructure (⟦ Γ ⟧Context → ⟦ τ ⟧Type)
  ichangeStructureΓτ {Γ} {τ} = changeStructureΓτ Γ τ
