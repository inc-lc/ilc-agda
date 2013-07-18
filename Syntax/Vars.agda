module Syntax.Vars
     {Type : Set}
  where

-- The notion of sets of variables
--
-- This module is calculus-independent.

open import Syntax.Context {Type}

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum

-- Sets of variables
data Vars : Context → Set where
  ∅ : Vars ∅
  lack : ∀ {τ Γ} → (x : Vars Γ) → Vars (τ • Γ)
  have : ∀ {τ Γ} → (x : Vars Γ) → Vars (τ • Γ)

none : {Γ : Context} → Vars Γ
none {∅} = ∅
none {τ • Γ} = lack (none {Γ})

singleton : ∀ {τ Γ} → Var Γ τ → Vars Γ
singleton {Γ = τ • Γ₀} this = have none
singleton (that x) = lack (singleton x)

tail : ∀ {τ Γ} → Vars (τ • Γ) → Vars Γ
tail (lack S) = S
tail (have S) = S

-- Union of variable sets
infixl 6 _∪_ -- just like _+_
_∪_ : ∀ {Γ} → Vars Γ → Vars Γ → Vars Γ
∅ ∪ ∅ = ∅
lack S₀ ∪ lack S₁ = lack (S₀ ∪ S₁)
lack S₀ ∪ have S₁ = have (S₀ ∪ S₁)
have S₀ ∪ lack S₁ = have (S₀ ∪ S₁)
have S₀ ∪ have S₁ = have (S₀ ∪ S₁)

-- Test if a set of variables is empty
empty? : ∀ {Γ} → (vs : Vars Γ) → (vs ≡ none) ⊎ ⊤
empty? ∅ = inj₁ refl
empty? (have vs) = inj₂ tt
empty? (lack vs) with empty? vs
... | inj₁ vs=∅ = inj₁ (cong lack vs=∅)
... | inj₂ _ = inj₂ tt
