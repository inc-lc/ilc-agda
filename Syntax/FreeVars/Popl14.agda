module Syntax.FreeVars.Popl14 where

-- Free variables of Calculus Popl14
--
-- Contents
-- FV: get the free variables of a term
-- closed?: test if a term is closed, producing a witness if yes.

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Base.Syntax.Vars Type public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Sum

FV : ∀ {τ Γ} → Term Γ τ → Vars Γ
FV-terms : ∀ {Σ Γ} → Terms Γ Σ → Vars Γ

FV (const ι ts) = FV-terms ts
FV (var x) = singleton x
FV (abs t) = tail (FV t)
FV (app s t) = FV s ∪ FV t

FV-terms ∅ = none
FV-terms (t • ts) = FV t ∪ FV-terms ts

closed? : ∀ {τ Γ} → (t : Term Γ τ) → (FV t ≡ none) ⊎ ⊤
closed? t = empty? (FV t)
