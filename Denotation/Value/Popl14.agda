module Denotation.Value.Popl14 where

open import Syntax.Type.Popl14 public
open import Base.Denotation.Notation public

open import Structure.Bag.Popl14
open import Data.Integer

-- Values of Calculus Popl14
--
-- Contents
-- - Domains associated with types
-- - `diff` and `apply` in semantic domains

⟦_⟧Type : Type -> Set
⟦ int ⟧Type = ℤ
⟦ bag ⟧Type = Bag
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type

meaningOfType : Meaning Type
meaningOfType = meaning ⟦_⟧Type

-- `diff` and `apply`
infixl 6 _⟦⊕⟧_ _⟦⊝⟧_
_⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
_⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

_⟦⊕⟧_ {int}  n Δn = n +  Δn
_⟦⊕⟧_ {bag}  b Δb = b ++ Δb
_⟦⊕⟧_ {σ ⇒ τ} f Δf = λ v → f v ⟦⊕⟧ Δf v (v ⟦⊝⟧ v)

_⟦⊝⟧_ {int}  m n = m -  n
_⟦⊝⟧_ {bag}  a b = a \\ b
_⟦⊝⟧_ {σ ⇒ τ} g f = λ v Δv → g (v ⟦⊕⟧ Δv) ⟦⊝⟧ f v
