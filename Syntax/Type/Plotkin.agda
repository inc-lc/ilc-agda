module Syntax.Type.Plotkin where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

infixr 5 _⇒_

data Type (B : Set {- of base types -}) : Set where
  base : (ι : B) → Type B
  _⇒_ : (σ : Type B) → (τ : Type B) → Type B

-- Lift (Δ : B → B) to (Δtype : Type B → Type B)
-- according to Δ (σ ⇒ τ) = σ ⇒ Δ σ ⇒ Δ τ
lift₀ : ∀ {B} → (B → B) → (Type B → Type B)
lift₀ f (base ι) = base (f ι)
lift₀ f (σ ⇒ τ) = let Δ = lift₀ f in σ ⇒ Δ σ ⇒ Δ τ

-- Lift (Δ : B → Type B) to (Δtype : Type B → Type B)
-- according to Δ (σ ⇒ τ) = σ ⇒ Δ σ ⇒ Δ τ
lift₁ : ∀ {B} → (B → Type B) → (Type B → Type B)
lift₁ f (base ι) = f ι
lift₁ f (σ ⇒ τ) = let Δ = lift₁ f in σ ⇒ Δ σ ⇒ Δ τ
