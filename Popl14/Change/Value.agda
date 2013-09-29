module Popl14.Change.Value where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value

open import Data.Integer
open import Structure.Bag.Popl14

-- `diff` and `apply`, without validity proofs
infixl 6 _⟦⊕⟧_ _⟦⊝⟧_
_⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
_⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

_⟦⊕⟧_ {base base-int}  n Δn = n +  Δn
_⟦⊕⟧_ {base base-bag}  b Δb = b ++ Δb
_⟦⊕⟧_ {σ ⇒ τ} f Δf = λ v →
  let
    _-₀_ = _⟦⊝⟧_ {σ}
    _+₁_ = _⟦⊕⟧_ {τ}
  in
    f v +₁ Δf v (v -₀ v)

_⟦⊝⟧_ {base base-int}  m n = m -  n
_⟦⊝⟧_ {base base-bag}  a b = a \\ b
_⟦⊝⟧_ {σ ⇒ τ} g f = λ v Δv → _⟦⊝⟧_ {τ} (g (_⟦⊕⟧_ {σ} v Δv)) (f v)
