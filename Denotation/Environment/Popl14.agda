module Denotation.Environment.Popl14 where

-- Environment of Calculus Popl14
--
-- Contents
-- - Environment specialized to Calculus Popl14

open import Denotation.Value.Popl14 public
import Denotation.Environment Type ⟦_⟧Type as Env
open Env public hiding (lift-sound)

open import Syntax.Context.Popl14
open import Denotation.Notation
open import Relation.Binary.PropositionalEquality

weakenVar-sound : ∀ {Γ₁ Γ₂ τ} (subctx : Γ₁ ≼ Γ₂) (x : Var Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weakenVar subctx x ⟧ ρ ≡ ⟦ x ⟧ (⟦ subctx ⟧ ρ)
weakenVar-sound = Env.lift-sound

