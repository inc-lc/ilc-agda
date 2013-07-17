module Syntax.Context.Plotkin where

-- Context for Plotkin-stype language descriptions
--
-- Duplicates Syntax.Context to a large extent.
-- Consider having Syntax.Context import this module.

infixr 9 _•_

data Context {Type : Set} : Set where
  ∅ : Context {Type}
  _•_ : (τ : Type) (Γ : Context {Type}) → Context {Type}

data Var {Type : Set} : Context → Type → Set where
  this : ∀ {Γ τ} → Var (τ • Γ) τ
  that : ∀ {Γ τ τ′} → (x : Var Γ τ) → Var (τ′ • Γ) τ
