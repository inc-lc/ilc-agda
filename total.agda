module total where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * Δ e describes how e changes when its free variables or its arguments change
--   * denotational semantics including semantics of changes
--
-- Note that Δ is *not* the same as the ∂ operator in
-- definition/intro.tex. See discussion at:
--
--   https://github.com/ps-mr/ilc/pull/34#discussion_r4290325
--
-- Work in Progress:
--   * lemmas about behavior of changes
--   * lemmas about behavior of Δ
--   * correctness proof for symbolic derivation

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Changes

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence
open import Denotational.ValidChanges

open import Changes
open import ChangeContexts
open import ChangeContextLifting
open import PropsDelta
open import SymbolicDerivation

-- CORRECTNESS of derivation

derive-var-correct : ∀ {Γ τ} → (ρ : ⟦ Δ-Context Γ ⟧) → (x : Var Γ τ) →
  diff (⟦ x ⟧ (update ρ)) (⟦ x ⟧ (ignore ρ)) ≡
  ⟦ derive-var x ⟧ ρ
derive-var-correct (dv • v • ρ) this = diff-apply dv v
derive-var-correct (dv • v • ρ) (that x) = derive-var-correct ρ x

derive-term-correct : ∀ {Γ₁ Γ₂ τ} → {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} → (t : Term Γ₁ τ) →
  Δ {{Γ′}} t ≈ derive-term {{Γ′}} t
derive-term-correct {Γ₁} {{Γ′}} (abs {τ} t) =
  begin
     Δ (abs t)
  ≈⟨  Δ-abs t  ⟩
     abs (abs (Δ {τ • Γ₁} t))
  ≈⟨  ≈-abs (≈-abs (derive-term-correct {τ • Γ₁} t))  ⟩
     abs (abs (derive-term {τ • Γ₁} t))
  ≡⟨⟩
     derive-term (abs t)
  ∎ where
      open ≈-Reasoning
      Γ″ = keep Δ-Type τ • keep τ • Γ′
derive-term-correct {Γ₁} {{Γ′}} (app t₁ t₂) =
  begin
    Δ (app t₁ t₂)
  ≈⟨  Δ-app t₁ t₂  ⟩
     app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂)
  ≈⟨  ≈-app (≈-app (derive-term-correct {{Γ′}} t₁) ≈-refl) (derive-term-correct {{Γ′}} t₂)  ⟩
     app (app (derive-term {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (derive-term {{Γ′}} t₂)
  ≡⟨⟩
    derive-term {{Γ′}} (app t₁ t₂)
  ∎ where open ≈-Reasoning
derive-term-correct {Γ₁} {{Γ′}} (var x) = ext-t (λ ρ →
  begin
    ⟦ Δ {{Γ′}} (var x) ⟧ ρ
  ≡⟨⟩
    diff
      (⟦ x ⟧ (update (⟦ Γ′ ⟧ ρ)))
      (⟦ x ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
  ≡⟨  derive-var-correct {Γ₁} (⟦ Γ′ ⟧ ρ) x  ⟩
    ⟦ derive-var x ⟧Var (⟦ Γ′ ⟧ ρ)
  ≡⟨ sym (lift-sound Γ′ (derive-var x) ρ) ⟩
    ⟦ lift Γ′ (derive-var x) ⟧Var ρ
  ∎) where open ≡-Reasoning
derive-term-correct true = ext-t (λ ρ → ≡-refl)
derive-term-correct false = ext-t (λ ρ → ≡-refl)
derive-term-correct {{Γ′}} (if t₁ t₂ t₃) =
  begin
    Δ (if t₁ t₂ t₃)
  ≈⟨ {!!} ⟩
    if (derive-term t₁ and lift-term {{Γ′}} t₁)
       (diff-term
         (apply-term (derive-term t₃)
         (lift-term {{Γ′}} t₃)) (lift-term {{Γ′}} t₂))
       (if (derive-term t₁ and (lift-term {{Γ′}} (! t₁)))
           (diff-term
             (apply-term (derive-term t₂)
             (lift-term {{Γ′}} t₂)) (lift-term {{Γ′}} t₃))
           (if (lift-term {{Γ′}} t₁)
             (derive-term t₂)
             (derive-term t₃)))
  ≡⟨⟩
    derive-term {{Γ′}} (if t₁ t₂ t₃)
  ∎ where open ≈-Reasoning

derive-term-correct (Δ t) = ≈-Δ (derive-term-correct t)
