module Syntax.Type.Plotkin where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

open import Function

infixr 5 _⇒_

data Type (B : Set {- of base types -}) : Set where
  base : (ι : B) → Type B
  _⇒_ : (σ : Type B) → (τ : Type B) → Type B

-- Lift (Δ : B → Type B) to (Δtype : Type B → Type B)
-- according to Δ (σ ⇒ τ) = σ ⇒ Δ σ ⇒ Δ τ
lift-Δtype : ∀ {B} → (B → Type B) → (Type B → Type B)
lift-Δtype f (base ι) = f ι
lift-Δtype f (σ ⇒ τ) = let Δ = lift-Δtype f in σ ⇒ Δ σ ⇒ Δ τ

-- Note: the above is *not* a monadic bind.
--
-- Proof. base` is the most straightforward `return` of the
-- functor `Type`.
--
--     return : B → Type B
--     return = base
--
-- Let
--
--     m : Type B
--     m = base κ ⇒ base ι
--
-- then
--
--     m >>= return = lift-Δtype return m
--                  = base κ ⇒ base κ ⇒ base ι
--
-- violating the second monadic law, m >>= return ≡ m. ∎

-- Variant of lift-Δtype for (Δ : B → B).
lift-Δtype₀ : ∀ {B} → (B → B) → (Type B → Type B)
lift-Δtype₀ f = lift-Δtype $ base ∘ f
-- This has a similar type to the type of `fmap`,
-- and `base` has a similar type to the type of `return`.
--
-- Similarly, for collections map can be defined from flatMap,
-- like lift-Δtype₀ can be defined in terms of lift-Δtype.
