module Base.Syntax.Vars
     (Type : Set)
  where

-- The notion of sets of variables
--
-- This module is calculus-independent.

open import Base.Syntax.Context Type

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum
open import Data.Bool

-- Sets of variables

open import Base.Data.DependentList public

Free : Type → Set
Free _ = Bool

Vars : Context → Set
Vars = DependentList Free

none : {Γ : Context} → Vars Γ
none = tabulate (λ _ → false)

singleton : ∀ {τ Γ} → Var Γ τ → Vars Γ
singleton {Γ = τ • Γ₀} this = true • none
singleton (that x) = false • singleton x

-- Union of variable sets
infixl 6 _∪_ -- just like _+_
_∪_ : ∀ {Γ} → Vars Γ → Vars Γ → Vars Γ
_∪_ = zipWith _∨_

-- Test if a set of variables is empty
empty? : ∀ {Γ} → (vs : Vars Γ) → (vs ≡ none) ⊎ ⊤
empty? ∅ = inj₁ refl
empty? (true • vs) = inj₂ tt
empty? (false • vs) with empty? vs
... | inj₁ vs=∅ = inj₁ (cong₂ _•_ refl vs=∅)
... | inj₂ _ = inj₂ tt
