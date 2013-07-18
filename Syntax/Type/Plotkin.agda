module Syntax.Type.Plotkin where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

infixr 5 _⇒_

data Type (B : Set {- of base types -}) : Set where
  base : (ι : B) → Type B
  _⇒_ : (σ : Type B) → (τ : Type B) → Type B

-- Lift (Δ : B → Type B) to (Δtype : Type B → Type B)
-- according to Δ (σ ⇒ τ) = σ ⇒ Δ σ ⇒ Δ τ
lift₁ : ∀ {B} → (B → Type B) → (Type B → Type B)
lift₁ f (base ι) = f ι
lift₁ f (σ ⇒ τ) = let Δ = lift₁ f in σ ⇒ Δ σ ⇒ Δ τ

-- Note: the above is monadic bind with a different argument order.

open import Function

-- Variant of lift₁ for (Δ : B → B).
lift₀ : ∀ {B} → (B → B) → (Type B → Type B)
lift₀ f = lift₁ $ base ∘ f
-- If lift₁ is a monadic bind, this is fmap,
-- and base is return.
--
-- Similarly, for collections map can be defined from flatMap, like lift₀ can be
-- defined in terms of lift₁.
