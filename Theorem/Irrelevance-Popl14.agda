module Theorem.Irrelevance-Popl14 where

-- Irrelevancy proofs:
--
-- All that's left after ΔEnv moves out.

open import Structure.Tuples public -- re-export `cons` constructor
open import Base.Denotation.Notation public
open import Popl14.Denotation.Value public
open import Popl14.Change.Validity public
open import Popl14.Change.Value public
open import Popl14.Change.Environment public 

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Bool

pattern have x = true • x
pattern lack x = false • x

-- Irrelevance: A set of variables is irrelevant in a ΔEnv
-- if their associated changes have no effect when applied.
irrelevant : ∀ {Γ} (S : Vars Γ) (ρ : ΔEnv Γ) → Set
irrelevant {∅} ∅ ∅ = ⊤
irrelevant {τ • Γ} (lack S) (cons _ _ _ ρ) = irrelevant S ρ
irrelevant {τ • Γ} (have S) (cons v Δv _ ρ) =
  (v ⊞₍ τ ₎ Δv ≡ v)   ×   (irrelevant S ρ)

-- Project irrelevance onto subsets of variables
project-irrelevance : ∀ {Γ : Context} {ρ : ΔEnv Γ} {R S} →
  irrelevant (R ∪ S) ρ → irrelevant R ρ × irrelevant S ρ
project-irrelevance {∅} {∅} {∅} {∅} tt = tt , tt
project-irrelevance {R = lack R} {lack S} I =
  project-irrelevance {R = R} {S} I
project-irrelevance {R = lack R} {have S} (eq , I) =
  let IR , IS = project-irrelevance {R = R} {S} I
  in IR , (eq , IS)
project-irrelevance {R = have R} {lack S} (eq , I) =
  let IR , IS = project-irrelevance {R = R} {S} I
  in (eq , IR) , IS
project-irrelevance {R = have R} {have S} (eq , I) =
  let IR , IS = project-irrelevance {R = R} {S} I
  in (eq , IR) , (eq , IS)

-- The empty set of variables is irrelevant in all environments
irrelevance : ∀ {Γ} {ρ : ΔEnv Γ} → irrelevant none ρ
irrelevance {∅} {∅} = tt
irrelevance {τ • Γ} {cons _ _ _ ρ} = irrelevance {ρ = ρ}

-- Semantic properties of special subcontext relations
⟦Γ≼Γ⟧ : ∀ {Γ} {ρ : ⟦ Γ ⟧} → ⟦ ≼-refl {Γ} ⟧ ρ ≡ ρ
⟦Γ≼Γ⟧ {∅} {∅} = refl
⟦Γ≼Γ⟧ {τ • Γ} {v • ρ} = cong₂ _•_ {x = v} refl (⟦Γ≼Γ⟧ {Γ} {ρ})
