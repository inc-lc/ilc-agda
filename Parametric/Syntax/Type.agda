module Parametric.Syntax.Type
  (Base : Set)
  where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

infixr 5 _⇒_

data Type : Set where
  base : (ι : Base) → Type
  _⇒_ : (σ : Type) → (τ : Type) → Type
