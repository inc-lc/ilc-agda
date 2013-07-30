module experimental.NormalizationByEvaluation where

-- NORMALIZATION BY EVALUATION
--
-- for the simply-typed λ calculus with base types

open import Level hiding (Lift; lift)
open import Data.Bool

open import Relation.Binary hiding (_⇒_)

-- The rest of this file is parametric in the set of base types.

module Parametric (Base : Set) where

  -- SYNTAX OF TYPES
  --
  -- We support function types and base types.

  data Type : Set where
    _⇒_ : (τ₁ τ₂ : Type) → Type
    base : (b : Base) → Type

  open import Syntax.Context Type public

  -- DOMAIN CONSTRUCTION
  --
  -- The meaning of types is defined using Kripke structures.

  record IsKripke {w ℓ₁ ℓ₂} {World : Set w}
                  (_≈_ : Rel World ℓ₁)
                  (_≤_ : Rel World ℓ₂)
                  (_⊩⟦_⟧Base : World → Base → Set (ℓ₂ ⊔ w))
                  : Set (w ⊔ ℓ₁ ⊔ ℓ₂) where
    Lift : ∀ {A : Set} (_⊩⟦_⟧ : World → A → Set (ℓ₂ ⊔ w)) → Set (ℓ₂ ⊔ w)
    Lift _⊩⟦_⟧ = ∀ {a w₁ w₂} → w₁ ≤ w₂ → w₁ ⊩⟦ a ⟧ → w₂ ⊩⟦ a ⟧

    field
      isPreorder : IsPreorder _≈_ _≤_
      liftBase : Lift _⊩⟦_⟧Base

    open IsPreorder isPreorder public

    _⊩⟦_⟧Type : World → Type → Set (ℓ₂ ⊔ w)
    w₁ ⊩⟦ τ₁ ⇒ τ₂ ⟧Type = ∀ {w₂} → w₁ ≤ w₂ → w₂ ⊩⟦ τ₁ ⟧Type → w₂ ⊩⟦ τ₂ ⟧Type
    w₁ ⊩⟦ base b ⟧Type = w₁ ⊩⟦ b ⟧Base

    liftType : Lift _⊩⟦_⟧Type
    liftType {τ₁ ⇒ τ₂} w₁≤w₂ w₁⊩τ₁⇒τ₂ = λ w₂≤w₃ w₃⊩τ₁ → w₁⊩τ₁⇒τ₂ (trans w₁≤w₂ w₂≤w₃) w₃⊩τ₁
    liftType {base b} w₁≤w₂ w₁⊩b = liftBase w₁≤w₂ w₁⊩b

    module _ (w : World) where
      open import Denotation.Environment Type (λ τ → w ⊩⟦ τ ⟧Type) public
        renaming (⟦_⟧Context to _⊩⟦_⟧Context; ⟦_⟧Var to _⊩⟦_⟧Var)

    liftContext : Lift {Context} _⊩⟦_⟧Context
    liftContext {∅} w₁≤w₂ w₁⊩Γ = ∅
    liftContext {τ • Γ} w₁≤w₂ (w₁⊩τ • w₁⊩Γ) = liftType {τ} w₁≤w₂ w₁⊩τ • liftContext w₁≤w₂ w₁⊩Γ

  record Kripke w ℓ₁ ℓ₂ : Set (suc (w ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      World : Set w
      _≈_ : Rel World ℓ₁
      _≤_ : Rel World ℓ₂
      _⊩⟦_⟧Base : World → Base → Set (ℓ₂ ⊔ w)
      isKripke : IsKripke _≈_ _≤_ _⊩⟦_⟧Base

    open IsKripke isKripke public

  -- TERMS
  --
  -- The syntax of terms is parametric in the set of constants.

  module Terms (Constant : Type → Set) where
    data Term : Context → Type → Set where
      abs : ∀ {Γ τ₁ τ₂} → (t : Term (τ₁ • Γ) τ₂) → Term Γ (τ₁ ⇒ τ₂)
      app : ∀ {Γ τ₁ τ₂} → (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) → Term Γ τ₂
      var : ∀ {Γ τ} → (x : Var Γ τ) → Term Γ τ
      con : ∀ {Γ τ} → (c : Constant τ) → Term Γ τ

    weaken : ∀ {Γ₁ Γ₂ τ} → Γ₁ ≼ Γ₂ → Term Γ₁ τ → Term Γ₂ τ
    weaken Γ₁≼Γ₂ (abs t) = abs (weaken (keep _ • Γ₁≼Γ₂) t)
    weaken Γ₁≼Γ₂ (app t₁ t₂) = app (weaken Γ₁≼Γ₂ t₁) (weaken Γ₁≼Γ₂ t₂)
    weaken Γ₁≼Γ₂ (var x) = var (lift Γ₁≼Γ₂ x)
    weaken Γ₁≼Γ₂ (con c) = con c

  -- SYMBOLIC EXECUTION and REIFICATION
  --
  -- The Kripke structure of symbolic computation, using typing
  -- contexts as worlds. Base types are interpreted as
  -- terms. This is parametric in the set of available constants.

  module Symbolic (Constant : Type → Set) where
    open import Relation.Binary.PropositionalEquality
    open Terms Constant

    BaseTerm : Context → Base → Set
    BaseTerm Γ b = Term Γ (base b)

    isKripke : IsKripke _≡_ _≼_ BaseTerm
    isKripke = record {
      isPreorder = ≼-isPreorder;
      liftBase = weaken }

    symbolic : Kripke zero zero zero
    symbolic = record {
      World = Context;
      _≈_ = _≡_;
      _≤_ = _≼_;
      _⊩⟦_⟧Base = BaseTerm;
      isKripke = isKripke }

    open Kripke symbolic

    ↓ : ∀ {Γ} τ → Γ ⊩⟦ τ ⟧Type → Term Γ τ
    ↑ : ∀ {Γ} τ → Term Γ τ → Γ ⊩⟦ τ ⟧Type

    ↓ (τ₁ ⇒ τ₂) v = abs (↓ τ₂ (v (drop τ₁ • ≼-refl) (↑ τ₁ (var this))))
    ↓ (base b) v = v

    ↑ (τ₁ ⇒ τ₂) t = λ Γ₁≼Γ₂ v → ↑ τ₂ (app (weaken Γ₁≼Γ₂ t) (↓ τ₁ v))
    ↑ (base b) t = t

    Γ⊩Γ : ∀ {Γ} → Γ ⊩⟦ Γ ⟧Context
    Γ⊩Γ {∅} = ∅
    Γ⊩Γ {τ • Γ} = ↑ τ (var this) • liftContext (drop τ • ≼-refl) Γ⊩Γ

  -- EVALUATION
  --
  -- Evaluation is defined for every Kripke structure and every
  -- set of constants. We have to provide the interpretation of
  -- the constants in the choosen Kripke structure, though.
  module _ {w ℓ₁ ℓ₂} (K : Kripke w ℓ₁ ℓ₂) where
    open Kripke K

    module Evaluation (Constant : Type → Set)
                      (_⊩⟦_⟧Constant : ∀ w {τ} → Constant τ → w ⊩⟦ τ ⟧Type) where
      open Terms Constant

      _⊩⟦_⟧Term_ : ∀ w {Γ τ} → Term Γ τ → w ⊩⟦ Γ ⟧Context → w ⊩⟦ τ ⟧Type
      w₁ ⊩⟦ abs t ⟧Term w₁⊩Γ = λ {w₂} w₁≤w₂ w₂⊩τ₁ → w₂ ⊩⟦ t ⟧Term (w₂⊩τ₁ • liftContext w₁≤w₂ w₁⊩Γ)
      w₁ ⊩⟦ app t₁ t₂ ⟧Term w₁⊩Γ = (w₁ ⊩⟦ t₁ ⟧Term w₁⊩Γ) refl (w₁ ⊩⟦ t₂ ⟧Term w₁⊩Γ)
      w₁ ⊩⟦ var x ⟧Term w₁⊩Γ = (w₁ ⊩⟦ x ⟧Var) w₁⊩Γ
      w₁ ⊩⟦ con c ⟧Term w₁⊩Γ = w₁ ⊩⟦ c ⟧Constant

  -- NORMALIZATION
  --
  -- Given a set of constants and their interpretation in the
  -- Kripke structure for symbolic computation, we can normalize
  -- terms.

  module _ (Constant : Type → Set) where
    open Terms Constant
    open Symbolic Constant
    open Kripke symbolic

    module Normalization (_⊩⟦_⟧Constant : ∀ Γ {τ} → Constant τ → Γ ⊩⟦ τ ⟧Type) where
      open Evaluation symbolic Constant _⊩⟦_⟧Constant

      norm : ∀ {Γ τ} → Term Γ τ → Term Γ τ
      norm {Γ} {τ} t = ↓ τ (Γ ⊩⟦ t ⟧Term Γ⊩Γ)
