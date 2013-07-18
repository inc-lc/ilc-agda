module Syntax.Context.Plotkin where

-- Context for Plotkin-stype language descriptions
--
-- This module will tend to duplicate Syntax.Context to a large
-- extent. Consider having Syntax.Context specialize future
-- content of this module to maintain its interface.

infixr 9 _•_

data Context {Type : Set} : Set where
  ∅ : Context {Type}
  _•_ : (τ : Type) (Γ : Context {Type}) → Context {Type}

data Var {Type : Set} : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ
