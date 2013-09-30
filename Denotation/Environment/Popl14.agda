module Denotation.Environment.Popl14 where

-- Environment of Calculus Popl14
--
-- Contents
-- - Environment specialized to Calculus Popl14
-- - Rename `data Empty` to `EmptyEnv` so that it's unrelated to ⊥
-- - ΔEnv: validity-embedded environment of values and changes
-- - `ignore` and `update` for ΔEnv
-- - Irrelevance: proof that a set of variables are unchanging
--     in an ΔEnv, and its properties
-- - Semantic properties of special subcontext relations

open import Structure.Tuples public -- re-export `cons` constructor
open import Base.Denotation.Notation public
open import Popl14.Denotation.Value public
open import Popl14.Change.Validity public
open import Popl14.Change.Value public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Bool

pattern have x = true • x
pattern lack x = false • x

data EmptyEnv : Set where
  ∅ : EmptyEnv

ΔEnv : Context → Set

-- ΔEnv : Context → Set
ΔEnv ∅ = EmptyEnv
ΔEnv (τ • Γ) = Quadruple
  ⟦ τ ⟧
  (λ _ → ΔVal τ)
  (λ v dv → valid v dv)
  (λ _ _ _ → ΔEnv Γ)

ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
ignore {∅} ρ = ∅
ignore {τ • Γ} (cons v dv R[v,dv] ρ) = v • ignore ρ

update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
update {∅} ρ = ∅
update {τ • Γ} (cons v dv R[v,dv] ρ) = (v ⊞ dv) • update ρ

-- Irrelevance: A set of variables is irrelevant in a ΔEnv
-- if their associated changes have no effect when applied.
irrelevant : ∀ {Γ} (S : Vars Γ) (ρ : ΔEnv Γ) → Set
irrelevant {∅} ∅ ∅ = ⊤
irrelevant {τ • Γ} (lack S) (cons _ _ _ ρ) = irrelevant S ρ
irrelevant {τ • Γ} (have S) (cons v Δv _ ρ) =
  (v ⊞ Δv ≡ v)   ×   (irrelevant S ρ)

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
