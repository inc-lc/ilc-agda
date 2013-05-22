module PropsDelta where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence

open import Changes
open import ChangeContexts
open import ChangeContextLifting

-- PROPERTIES of Δ

Δ-abs : ∀ {τ₁ τ₂ Γ₁ Γ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t : Term (τ₁ • Γ₁) τ₂) →
  let Γ″ = keep Δ-Type τ₁ • keep τ₁ • Γ′ in
  Δ {{Γ′}} (abs t) ≈ abs (abs (Δ {τ₁ • Γ₁} t))
Δ-abs t = ext-t (λ ρ → refl)

Δ-app : ∀ {Γ₁ Γ₂ τ₁ τ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t₁ : Term Γ₁ (τ₁ ⇒ τ₂)) (t₂ : Term Γ₁ τ₁) →
  Δ {{Γ′}} (app t₁ t₂) ≈ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂)
Δ-app {{Γ′}} t₁ t₂ = ≈-sym (ext-t (λ ρ′ → let ρ = ⟦ Γ′ ⟧ ρ′ in
  begin
    ⟦ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂) ⟧ ρ′
  ≡⟨⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′))
  ≡⟨ ≡-cong
       (λ x →
          diff
          (⟦ t₁ ⟧ (update ρ)
           (apply (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) x))
          (⟦ t₁ ⟧ (ignore ρ) x))
       (lift-term-ignore {{Γ′}} t₂) ⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ t₂ ⟧ (ignore ρ))))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ≡⟨  ≡-cong
       (λ x →
          diff (⟦ t₁ ⟧ (update ρ) x) (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ))))
       (apply-diff (⟦ t₂ ⟧ (ignore ρ)) (⟦ t₂ ⟧ (update ρ)))  ⟩
    diff
      (⟦ t₁ ⟧ (update ρ) (⟦ t₂ ⟧ (update ρ)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ≡⟨⟩
     ⟦ Δ {{Γ′}} (app t₁ t₂) ⟧ ρ′
  ∎)) where open ≡-Reasoning
