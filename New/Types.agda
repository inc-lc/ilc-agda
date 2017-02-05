module New.Types where

open import Data.Integer
open import Data.Product
infixr 5 _⇒_

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  int : Type
  pair : (σ τ : Type) → Type

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ int ⟧Type = ℤ
⟦ pair σ τ ⟧Type = ⟦ σ ⟧Type × ⟦ τ ⟧Type

Δt : Type → Type
Δt (σ ⇒ τ) = σ ⇒ Δt σ ⇒ Δt τ
Δt int = int
Δt (pair σ τ) = pair (Δt σ) (Δt τ)
