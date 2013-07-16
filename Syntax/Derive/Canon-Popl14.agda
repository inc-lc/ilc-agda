module Syntax.Derive.Canon-Popl14 where

open import Syntax.Term.Popl14 public

open import Data.Integer

deriveVar : ∀ {τ Γ} → Var Γ τ → Var (ΔContext Γ) (ΔType τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

derive : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) (ΔType τ)
derive (int n) = int (+ 0)
derive (add s t) = add (derive s) (derive t)
derive (minus t) = minus (derive t)
derive empty = empty
derive (insert s t) =
  insert (fit s ⊕ derive s) (fit t ⊕ derive t) ⊝ insert (fit s) (fit t)
derive (union s t) = union (derive s) (derive t)
derive (negate t) = negate (derive t)
derive (flatmap s t) =
 flatmap (fit s ⊕ derive s) (fit t ⊕ derive t) ⊝ flatmap (fit s) (fit t)
derive (sum t) = sum (derive t)
derive (var x) = var (deriveVar x)
derive (app s t) = app (app (derive s) (fit t)) (derive t)
derive (abs t) = abs (abs (derive t))
