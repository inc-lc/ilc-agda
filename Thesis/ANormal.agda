--
-- Formalize correctness of differentiation for the source calculus in the
-- static caching paper (typed version).
--

module Thesis.ANormal where

open import Thesis.Types public
open import Thesis.Contexts public

open import Relation.Binary.PropositionalEquality

data Term (Γ : Context) (τ : Type) : Set where
  var : (x : Var Γ τ) →
    Term Γ τ
  lett : ∀ {σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → Term (τ₁ • Γ) τ → Term Γ τ

-- Also represent top-level definitions, so that we can somehow create functions
-- via syntax. Made up on the moment.

-- WARNING: this allows nested lambdas. That's more powerful than allowing only
-- closures whose bodies can't contain lambdas, like in the paper.
data Fun (Γ : Context) : (τ : Type) → Set where
  term : ∀ {τ} → Term Γ τ → Fun Γ τ
  abs : ∀ {σ τ} → Fun (σ • Γ) τ → Fun Γ (σ ⇒ τ)

open import Thesis.Environments public

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ lett f x t ⟧Term ρ = ⟦ t ⟧Term (⟦ f ⟧Var ρ (⟦ x ⟧Var ρ) • ρ)

⟦_⟧Fun : ∀ {Γ τ} → Fun Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ term t ⟧Fun ρ = ⟦ t ⟧Term ρ
⟦ abs f ⟧Fun ρ = λ v → ⟦ f ⟧Fun (v • ρ)

-- Next steps:
-- 1. Add a functional big-step semantics for this language: DONE.
-- 2. Prove it sound wrt. the denotational semantics: DONE.
-- 3. Add an erasure to a uni-typed language. DONE.
-- 4. Redo 1 with an *untyped* functional big-step semantics.
-- 5. Prove that evaluation and erasure commute:
-- -- erasure-commute-term : ∀ {Γ τ} (t : T.Term Γ τ) ρ n →
-- --   erase-errVal (T.eval-term t ρ n) ≡ eval-term (erase-term t) (erase-env ρ) n
-- 6. Define new caching transformation into untyped language.
--
-- 7. Prove the new transformation correct in the untyped language, by reusing
-- evaluation on the source language.
