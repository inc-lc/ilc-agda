module Thesis.SIRelBigStep.Types where

open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  nat : Type
infixr 20 _⇒_

open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public

-- Decidable equivalence for types and contexts. Needed later for ⊕ on closures.

⇒-inj : ∀ {τ1 τ2 τ3 τ4 : Type} → _≡_ {A = Type} (τ1 ⇒ τ2) (τ3 ⇒ τ4) → τ1 ≡ τ3 × τ2 ≡ τ4
⇒-inj refl = refl , refl

_≟Type_ : (τ1 τ2 : Type) → Dec (τ1 ≡ τ2)
(τ1 ⇒ τ2) ≟Type (τ3 ⇒ τ4) with τ1 ≟Type τ3 | τ2 ≟Type τ4
(τ1 ⇒ τ2) ≟Type (.τ1 ⇒ .τ2) | yes refl | yes refl = yes refl
(τ1 ⇒ τ2) ≟Type (.τ1 ⇒ τ4) | yes refl | no ¬q = no (λ x → ¬q (proj₂ (⇒-inj x)))
(τ1 ⇒ τ2) ≟Type (τ3 ⇒ τ4) | no ¬p | q = no (λ x → ¬p (proj₁ (⇒-inj x)))
(τ1 ⇒ τ2) ≟Type nat = no (λ ())
nat ≟Type (τ2 ⇒ τ3) = no (λ ())
nat ≟Type nat = yes refl

•-inj : ∀ {τ1 τ2 : Type} {Γ1 Γ2 : Context} → _≡_ {A = Context} (τ1 • Γ1) (τ2 • Γ2) → τ1 ≡ τ2 × Γ1 ≡ Γ2
•-inj refl = refl , refl

_≟Ctx_ : (Γ1 Γ2 : Context) → Dec (Γ1 ≡ Γ2)
∅ ≟Ctx ∅ = yes refl
∅ ≟Ctx (τ2 • Γ2) = no (λ ())
(τ1 • Γ1) ≟Ctx ∅ = no (λ ())
(τ1 • Γ1) ≟Ctx (τ2 • Γ2) with τ1 ≟Type τ2 | Γ1 ≟Ctx Γ2
(τ1 • Γ1) ≟Ctx (.τ1 • .Γ1) | yes refl | yes refl = yes refl
(τ1 • Γ1) ≟Ctx (.τ1 • Γ2) | yes refl | no ¬q = no (λ x → ¬q (proj₂ (•-inj x)))
(τ1 • Γ1) ≟Ctx (τ2 • Γ2) | no ¬p | q = no (λ x → ¬p (proj₁ (•-inj x)))

≟Ctx-refl : ∀ Γ → Γ ≟Ctx Γ ≡ yes refl
≟Ctx-refl Γ with Γ ≟Ctx Γ
≟Ctx-refl Γ | yes refl = refl
≟Ctx-refl Γ | no ¬p = ⊥-elim (¬p refl)
