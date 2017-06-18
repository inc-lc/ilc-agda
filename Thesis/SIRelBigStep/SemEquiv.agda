module Thesis.SIRelBigStep.SemEquiv where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Thesis.SIRelBigStep.Syntax public
open import Thesis.SIRelBigStep.OpSem
open import Thesis.SIRelBigStep.DenSem

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → ⟦ Γ ⟧Context → Den.⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Term) (v • ⟦ ρ ⟧Env)
⟦ natV n ⟧Val = n
⟦ pairV v1 v2 ⟧Val = ⟦ v1 ⟧Val , ⟦ v2 ⟧Val

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  Den.⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ ⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

eval-const-sound : ∀ {τ} (c : Const τ) → ⟦ c ⟧Const ≡ ⟦ eval-const c ⟧Val
eval-const-sound (lit n) = refl

eval-primitive-sound : ∀ {σ τ} (p : Primitive (σ ⇒ τ)) v → ⟦ p ⟧Primitive ⟦ v ⟧Val ≡ ⟦ eval-primitive p v ⟧Val
eval-primitive-sound succ (natV n) = refl
eval-primitive-sound add (pairV (natV n1) (natV n2)) = refl

eval-sound : ∀ {Γ τ} ρ (sv : SVal Γ τ) →
   ⟦ sv ⟧SVal ⟦ ρ ⟧Env ≡ ⟦ eval sv ρ ⟧Val
eval-sound ρ (var x) = ↦-sound ρ x
eval-sound ρ (abs t) = refl
eval-sound ρ (cons sv1 sv2) rewrite eval-sound ρ sv1 | eval-sound ρ sv2 = refl
eval-sound ρ (const c) = eval-const-sound c

-- Check it's fine to use i 1 in the above proofs.
↓-sv-1-step : ∀ {Γ τ ρ v} {n} {sv : SVal Γ τ} →
  ρ ⊢ val sv ↓[ i' n ] v →
  n ≡ 1
↓-sv-1-step (val sv) = refl

↓-sound : ∀ {Γ τ ρ v hasIdx} {n : Idx hasIdx} {t : Term Γ τ} →
  ρ ⊢ t ↓[ n ] v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
↓-sound (val sv) = eval-sound _ sv
↓-sound (app _ _ ↓₁ ↓₂ ↓′) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ | ↓-sound ↓′ = refl
↓-sound (lett n1 n2 vsv s t ↓ ↓₁) rewrite ↓-sound ↓ | ↓-sound ↓₁ = refl
↓-sound {ρ = ρ} (primapp p sv) rewrite eval-sound ρ sv = eval-primitive-sound p (eval sv ρ)
