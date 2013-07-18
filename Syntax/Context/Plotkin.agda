module Syntax.Context.Plotkin {Type : Set} where

-- Context for Plotkin-style language descriptions
--
-- This module will tend to duplicate Syntax.Context to a large
-- extent. Consider having Syntax.Context specialize future
-- content of this module to maintain its interface.

infixr 9 _•_

data Context : Set where
  ∅ : Context
  _•_ : (τ : Type) (Γ : Context) → Context

data Var : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ
