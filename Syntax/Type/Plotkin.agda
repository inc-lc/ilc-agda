module Syntax.Type.Plotkin where

-- Types for language description à la Plotkin (LCF as PL)
--
-- Given base types, we build function types.

open import Syntax.Language.Base

infixr 5 _⇒_

data Type (B : Set {- of base types -}) : Set where
  base : (ι : B) → Type B
  _⇒_ : (σ : Type B) → (τ : Type B) → Type B
