module Syntax.Type.Popl14 where

-- Types of Calculus Popl14

infixr 5 _⇒_

data Type : Set where
  int : Type
  bag : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

ΔType : Type → Type
ΔType int = int
ΔType bag = bag
ΔType (σ ⇒ τ) = σ ⇒ ΔType σ ⇒ ΔType τ
