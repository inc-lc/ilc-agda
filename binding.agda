module binding
    (Type : Set)
    (⟦_⟧Type : Type → Set)
  where

-- CONTEXTS
--
-- This module defines the syntax of contexts, prefixes of
-- contexts and variables and properties of these notions.
--
-- This module is parametric in the syntax of types, so it
-- can be reused for different calculi.

-- ENVIRONMENTS
--
-- This module defines the meaning of contexts, that is,
-- the type of environments that fit a context, together
-- with operations and properties of these operations.
--
-- This module is parametric in the syntax and semantics
-- of types, so it can be reused for different calculi
-- and models.

open import Denotational.Notation

private
  meaningOfType : Meaning Type
  meaningOfType = meaning ⟦_⟧Type

-- TYPING CONTEXTS

-- Syntax

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

infixr 9 _•_

-- Denotational Semantics : Contexts Represent Environments

data Empty : Set where
  ∅ : Empty

data Bind A B : Set where
  _•_ : (v : A) (ρ : B) → Bind A B

⟦_⟧Context : Context → Set
⟦ ∅ ⟧Context = Empty
⟦ τ • Γ ⟧Context = Bind ⟦ τ ⟧ ⟦ Γ ⟧Context

meaningOfContext : Meaning Context
meaningOfContext = meaning ⟦_⟧Context

-- VARIABLES

-- Syntax

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ

-- Denotational Semantics

⟦_⟧Var : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ this ⟧Var (v • ρ) = v
⟦ that x ⟧Var (v • ρ) = ⟦ x ⟧Var ρ

meaningOfVar : ∀ {Γ τ} → Meaning (Var Γ τ)
meaningOfVar = meaning ⟦_⟧Var

-- WEAKENING

-- Prefix of a context

data Prefix : Context → Set where
  ∅ : ∀ {Γ} → Prefix Γ
  _•_ : ∀ {Γ} → (τ : Type) → Prefix Γ → Prefix (τ • Γ)

-- take only the prefix of a context

take : (Γ : Context) → Prefix Γ → Context
take Γ ∅ = ∅
take (τ • Γ) (.τ • Γ′) = τ • take Γ Γ′

-- drop the prefix of a context

drop : (Γ : Context) → Prefix Γ → Context
drop Γ ∅ = Γ
drop (τ • Γ) (.τ • Γ′) = drop Γ Γ′

-- Extend a context to a super context

infixr 10 _⋎_

_⋎_ : (Γ₁ Γ₂ : Context) → Context
∅ ⋎ Γ₂ = Γ₂
(τ • Γ₁) ⋎ Γ₂ = τ • Γ₁ ⋎ Γ₂

-- Remove a variable from an environment

weakenEnv : ∀ Γ₁ τ₂ {Γ₃} → ⟦ Γ₁ ⋎ (τ₂ • Γ₃) ⟧ → ⟦ Γ₁ ⋎ Γ₃ ⟧
weakenEnv ∅ τ₂ (v • ρ) = ρ
weakenEnv (τ • Γ₁) τ₂ (v • ρ) = v • weakenEnv Γ₁ τ₂ ρ

open import Relation.Binary.PropositionalEquality

take-drop : ∀ Γ Γ′ → take Γ Γ′ ⋎ drop Γ Γ′ ≡ Γ
take-drop ∅ ∅ = refl
take-drop (τ • Γ) ∅ = refl
take-drop (τ • Γ) (.τ • Γ′) rewrite take-drop Γ Γ′ = refl

or-unit : ∀ Γ → Γ ⋎ ∅ ≡ Γ
or-unit ∅ = refl
or-unit (τ • Γ) rewrite or-unit Γ = refl

move-prefix : ∀ Γ τ Γ′ →
  Γ ⋎ (τ • Γ′) ≡ (Γ ⋎ (τ • ∅)) ⋎ Γ′
move-prefix ∅ τ Γ′ = refl
move-prefix (τ • Γ) τ₁ ∅ = sym (or-unit (τ • Γ ⋎ (τ₁ • ∅)))
move-prefix (τ • Γ) τ₁ (τ₂ • Γ′) rewrite move-prefix Γ τ₁ (τ₂ • Γ′) = refl

-- Lift a variable to a super context

lift : ∀ {Γ₁ Γ₂ Γ₃ τ} → Var (Γ₁ ⋎ Γ₃) τ → Var (Γ₁ ⋎ Γ₂ ⋎ Γ₃) τ
lift {∅} {∅} x = x
lift {∅} {τ • Γ₂} x = that (lift {∅} {Γ₂} x)
lift {τ • Γ₁} {Γ₂} this = this
lift {τ • Γ₁} {Γ₂} (that x) = that (lift {Γ₁} {Γ₂} x)
