module Thesis.LangChanges where

open import Thesis.Changes
open import Thesis.IntChanges
open import Thesis.Lang
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
[ int ]τ dv from v1 to v2 = v1 + dv ≡ v2
[ pair σ τ ]τ (da , db) from (a1 , b1) to (a2 , b2) = [ σ ]τ da from a1 to a2 × [ τ ]τ db from b1 to b2
[ sum σ τ ]τ dv from v1 to v2 = sch_from_to_ dv v1 v2

isCompChangeStructureτ (σ ⇒ τ) = ChangeStructure.isCompChangeStructure (funCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ int = ChangeStructure.isCompChangeStructure intCS
isCompChangeStructureτ (pair σ τ) = ChangeStructure.isCompChangeStructure (pairCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ (sum σ τ) = ChangeStructure.isCompChangeStructure ((sumCS {{changeStructureτ σ}} {{changeStructureτ τ}}))

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

  isEnvCompCS Γ = IsChangeStructure→IsCompChangeStructure (record
    { _⊕_ = _e⊕_
    ; fromto→⊕ = efromto→⊕
    ; _⊝_ = _e⊝_
    ; ⊝-fromto = e⊝-fromto
    } )

changeStructureΓ : ∀ Γ → ChangeStructure ⟦ Γ ⟧Context
changeStructureΓ Γ = record { isCompChangeStructure = isEnvCompCS Γ }

instance
  ichangeStructureΓ : ∀ {Γ} → ChangeStructure ⟦ Γ ⟧Context
  ichangeStructureΓ {Γ} = changeStructureΓ Γ
