{-

Communicate to derivatives that changes to certain arguments
are always nil (i. e., certain arguments are stable).

Checklist of stuff to add when adding syntactic constructs

- weaken
- ⟦_⟧Term
- weaken-sound
- derive (symbolic derivation)
- validity-of-derive
- correctness-of-derive

-}

module ExplicitNil where

open import Data.Bool
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)

open import Relation.Binary.PropositionalEquality

open import Level using
  (zero ; Level ; suc)
open import Relation.Binary using
  (Reflexive ; Transitive ; Preorder ; IsPreorder)

postulate extensionality : Extensionality zero zero

open import MapBag

data Arguments : (τ : Type) → Set where
  none : Arguments ints -- or all other base types
  constant : ∀ {τ₁ τ₂} → (args : Arguments τ₂) → Arguments (τ₁ ⇒ τ₂)
  volatile : ∀ {τ₁ τ₂} → (args : Arguments τ₂) → Arguments (τ₁ ⇒ τ₂)

-- Subcontext relation is isomorphic to subsets of variables.
-- We declare this relation again for a fitting concrete syntax alone.

data Variables : Context → Set where
  ∅ : Variables ∅
  _•_ : ∀ {τ Γ} → (is-inside : Bool) → Variables Γ → Variables (τ • Γ)

_∈_ : ∀ {τ Γ} → Var Γ τ → Variables Γ → Bool
this ∈ (is-inside • vars) = is-inside
that x ∈ (_ • vars) = x ∈ vars

FV_intersects_ : ∀ {τ Γ} → Term Γ τ → Variables Γ → Bool
FV (var x) intersects vars = not (x ∈ vars)
FV (int n) intersects vars = false
FV (abs t) intersects vars = FV t intersects (false • vars)
FV (app t₁ t₂) intersects vars = FV t₁ intersects vars ∨ FV t₂ intersects vars

FV_is-disjoint-from_ : ∀ {τ Γ} → Term Γ τ → Variables Γ → Bool
FV t is-disjoint-from vars = not (FV t intersects vars)

 

