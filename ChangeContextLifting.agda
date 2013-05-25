module ChangeContextLifting where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total

open import ChangeContexts

-- LIFTING terms into Δ-Contexts

lift-term : ∀ {Γ₁ Γ₂ τ} (Γ′ : Δ-Context Γ₁ ≼ Γ₂) → Term Γ₁ τ → Term Γ₂ τ
lift-term {Γ₁} {Γ₂} Γ′ = weaken (≼-trans ≼-Δ-Context Γ′)

-- PROPERTIES of lift-term

lift-term-ignore : ∀ {Γ₁ Γ₂ τ} (Γ′ : Δ-Context Γ₁ ≼ Γ₂) {ρ : ⟦ Γ₂ ⟧} (t : Term Γ₁ τ) →
  ⟦ lift-term Γ′ t ⟧ ρ ≡ ⟦ t ⟧ (ignore (⟦ Γ′ ⟧ ρ))
lift-term-ignore Γ′ {ρ} t = let Γ″ = ≼-trans ≼-Δ-Context Γ′ in
  begin
    ⟦ lift-term Γ′ t ⟧ ρ
  ≡⟨⟩
    ⟦ weaken Γ″ t ⟧ ρ
  ≡⟨ weaken-sound t ρ ⟩
    ⟦ t ⟧ (⟦ ≼-trans ≼-Δ-Context Γ′ ⟧ ρ)
  ≡⟨ cong (λ x → ⟦ t ⟧ x) (⟦⟧-≼-trans ≼-Δ-Context Γ′ ρ) ⟩
    ⟦ t ⟧Term (⟦ ≼-Δ-Context ⟧≼ (⟦ Γ′ ⟧≼ ρ))
  ≡⟨⟩
    ⟦ t ⟧ (ignore (⟦ Γ′ ⟧ ρ))
  ∎ where open ≡-Reasoning
