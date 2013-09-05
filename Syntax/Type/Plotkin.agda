module Syntax.Type.Plotkin
  (B : Set {- of base types -})
  where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

infixr 5 _⇒_

data Type : Set where
  base : (ι : B) → Type
  _⇒_ : (σ : Type) → (τ : Type) → Type


-- Lift (Δ : Base → Type Base) to (Δtype : Type Base → Type Base)
-- according to Δ (σ ⇒ τ) = σ ⇒ Δ σ ⇒ Δ τ
lift-Δtype : (B → Type) → (Type → Type)
lift-Δtype f (base ι) = f ι
lift-Δtype f (σ ⇒ τ) = let Δ = lift-Δtype f in σ ⇒ Δ σ ⇒ Δ τ
