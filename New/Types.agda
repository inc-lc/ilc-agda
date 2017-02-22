module New.Types where

open import Data.Integer public
open import Data.Product public hiding (map)
open import Data.Sum public hiding (map)
infixr 5 _⇒_

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  int : Type
  pair : (σ τ : Type) → Type
  sum : (σ τ : Type) → Type

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ int ⟧Type = ℤ
⟦ pair σ τ ⟧Type = ⟦ σ ⟧Type × ⟦ τ ⟧Type
⟦ sum σ τ ⟧Type = ⟦ σ ⟧Type ⊎ ⟦ τ ⟧Type

Δt : Type → Type
Δt (σ ⇒ τ) = σ ⇒ Δt σ ⇒ Δt τ
Δt int = int
Δt (pair σ τ) = pair (Δt σ) (Δt τ)
Δt (sum σ τ) = sum (sum (Δt σ) (Δt τ)) (sum σ τ)
