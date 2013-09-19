module Syntax.Derive.Optimized-Popl14 where

open import Popl14.Change.Term public
open import Syntax.Derive.Canon-Popl14 public using (deriveVar; fit)

open import Data.Sum
open import Data.Integer
open import Syntax.FreeVars.Popl14

derive+ : ∀ {τ Γ} → Term Γ τ → Term (ΔContext Γ) (ΔType τ)
derive+ (intlit n) = intlit (+ 0)
derive+ (add s t) = add (derive+ s) (derive+ t)
derive+ (minus t) = minus (derive+ t)
derive+ empty = empty
derive+ (insert s t) with closed? s
... | inj₁ is-closed = derive+ t
... | inj₂ tt =
  insert (apply {int} (derive+ s) (fit s)) (apply {bag} (derive+ t) (fit t)) ⊝ insert (fit s) (fit t)
derive+ (union s t) = union (derive+ s) (derive+ t)
derive+ (negate t) = negate (derive+ t)
derive+ (flatmap s t) with closed? s
... | inj₁ is-closed = flatmap (fit s) (derive+ t)
... | inj₂ tt =
  flatmap (apply {int ⇒ bag} (derive+ s) (fit s)) (apply {bag} (derive+ t) (fit t)) ⊝ flatmap (fit s) (fit t)
derive+ (sum t) = sum (derive+ t)
derive+ (var x) = var (deriveVar x)
derive+ (app s t) = app (app (derive+ s) (fit t)) (derive+ t)
derive+ (abs t) = abs (abs (derive+ t))
