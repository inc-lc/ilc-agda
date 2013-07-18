module Syntax.FreeVars.Popl14 where

-- Free variables of Calculus Popl14
--
-- Contents
-- FV: get the free variables of a term
-- closed?: test if a term is closed, producing a witness if yes.

open import Syntax.Type.Popl14
open import Syntax.Term.Popl14
open import Syntax.Vars {Type} public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum

FV : ∀ {τ Γ} → Term Γ τ → Vars Γ
FV {Γ = Γ} (int n) = none
FV (add s t) = FV s ∪ FV t
FV (minus t) = FV t

FV {Γ = Γ} empty = none
FV (insert s t) = FV s ∪ FV t
FV (union s t) = FV s ∪ FV t
FV (negate t) = FV t

FV (flatmap s t) = FV s ∪ FV t
FV (sum t) = FV t

FV (var x) = singleton x
FV (abs t) = tail (FV t)
FV (app s t) = FV s ∪ FV t

closed? : ∀ {τ Γ} → (t : Term Γ τ) → (FV t ≡ none) ⊎ ⊤
closed? t = empty? (FV t)
