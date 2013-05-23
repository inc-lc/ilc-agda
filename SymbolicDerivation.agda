module SymbolicDerivation where

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

open import Natural.Evaluation

open import Changes
open import ChangeContexts
open import ChangeContextLifting
open import PropsDelta

-- SYMBOLIC DERIVATION

derive-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
derive-var {τ • Γ} this = this
derive-var {τ • Γ} (that x) = that (that (derive-var x))

derive-term : ∀ {Γ₁ Γ₂ τ} → {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} → Term Γ₁ τ → Term Γ₂ (Δ-Type τ)
derive-term {Γ₁} {{Γ′}} (abs {τ} t) = abs (abs (derive-term {τ • Γ₁} {{Γ″}} t))
  where Γ″ = keep Δ-Type τ • keep τ • Γ′
derive-term {{Γ′}} (app t₁ t₂) = app (app (derive-term {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (derive-term {{Γ′}} t₂)
derive-term {{Γ′}} (var x) = var (lift Γ′ (derive-var x))
derive-term {{Γ′}} true = false
derive-term {{Γ′}} false = false
derive-term {{Γ′}} (if c t e) =
  if ((derive-term {{Γ′}} c) and (lift-term {{Γ′}} c))
     (diff-term
       (apply-term (derive-term {{Γ′}} e) (lift-term {{Γ′}} e))
       (lift-term {{Γ′}} t))
     (if ((derive-term {{Γ′}} c) and (lift-term {{Γ′}} (! c)))
       (diff-term
         (apply-term (derive-term {{Γ′}} t) (lift-term {{Γ′}} t))
         (lift-term {{Γ′}} e))
       (if (lift-term {{Γ′}} c)
         (derive-term {{Γ′}} t)
         (derive-term {{Γ′}} e)))
derive-term {{Γ′}} (Δ {{Γ″}} t) = Δ {{Γ′}} (derive-term {{Γ″}} t)
