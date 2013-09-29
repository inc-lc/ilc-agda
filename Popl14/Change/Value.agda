module Popl14.Change.Value where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value

open import Data.Integer
open import Structure.Bag.Popl14

-- `diff` and `apply`, without validity proofs
⟦apply⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
⟦diff⟧ : ∀ τ → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

infixl 6 ⟦apply⟧ ⟦diff⟧
syntax ⟦apply⟧ τ v dv = v ⟦⊕₍ τ ₎⟧ dv
syntax ⟦diff⟧ τ u v = u ⟦⊝₍ τ ₎⟧ v

n ⟦⊕₍ base base-int ₎⟧ Δn = n +  Δn
b ⟦⊕₍ base base-bag ₎⟧ Δb = b ++ Δb
f ⟦⊕₍ σ ⇒ τ ₎⟧ Δf = λ v → f v ⟦⊕₍ τ ₎⟧ Δf v (v ⟦⊝₍ σ ₎⟧ v)

m ⟦⊝₍ base base-int ₎⟧ n = m -  n
a ⟦⊝₍ base base-bag ₎⟧ b = a \\ b
g ⟦⊝₍ σ ⇒ τ ₎⟧ f = λ v Δv → (g (v ⟦⊕₍ σ ₎⟧ Δv)) ⟦⊝₍ τ ₎⟧ (f v)

_⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
_⟦⊕⟧_ {τ} = ⟦apply⟧ τ

_⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
_⟦⊝⟧_ {τ} = ⟦diff⟧ τ
