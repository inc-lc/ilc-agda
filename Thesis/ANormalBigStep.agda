module Thesis.ANormalBigStep where

open import Base.Data.DependentList public
open import Data.Nat.Base
open import Data.Integer
open import Relation.Binary.PropositionalEquality

open import Thesis.ANormal

data Val : Type → Set
-- data Val (τ : Type) : Set

import Base.Denotation.Environment
module Op = Base.Denotation.Environment Type Val

-- data Val (τ : Type) where
data Val where
  closure : ∀ {Γ σ τ} → (t : Fun (σ • Γ) τ) → (ρ : Op.⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  intV : ∀ (n : ℤ) → Val int

data ErrVal (τ : Type) : Set where
  Done : (v : Val τ) → ErrVal τ
  Error : ErrVal τ
  TimeOut : ErrVal τ

_>>=_ : ∀ {σ τ} → ErrVal σ → (Val σ → ErrVal τ) → ErrVal τ
Done v >>= f = f v
Error >>= f = Error
TimeOut >>= f = TimeOut

Res : Type → Set
Res τ = ℕ → ErrVal τ

eval-fun : ∀ {Γ τ} → Fun Γ τ → Op.⟦ Γ ⟧Context → Res τ
eval-term : ∀ {Γ τ} → Term Γ τ → Op.⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure f ρ) a n = eval-fun f (a • ρ) n

eval-term t ρ zero = TimeOut
eval-term (var x) ρ (suc n) = Done (Op.⟦ x ⟧Var ρ)
eval-term (lett f x t) ρ (suc n) = apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n >>= (λ v → eval-term t (v • ρ) n)

eval-fun (term t) ρ n = eval-term t ρ n
eval-fun (abs f) ρ n = Done (closure f ρ)

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → Op.⟦ Γ ⟧Context → ⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Fun) (v • ⟦ ρ ⟧Env)
⟦ intV n ⟧Val = n

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  ⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ Op.⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

eval-term-sound : ∀ {Γ τ} ρ v n (t : Term Γ τ) →
  eval-term t ρ n ≡ Done v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

eval-fun-sound : ∀ {Γ τ} ρ v n (t : Fun Γ τ) →
  eval-fun t ρ n ≡ Done v →
  ⟦ t ⟧Fun ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

-- XXX Here we only need a degenerate form of this lemma, for variables.
apply-sound : ∀ {Γ σ τ} ρ v f a n (s : Term Γ (σ ⇒ τ)) t →
  ⟦ s ⟧Term ⟦ ρ ⟧Env ≡ ⟦ f ⟧Val →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ a ⟧Val →
  apply f a n ≡ Done v →
  ⟦ s ⟧Term ⟦ ρ ⟧Env (⟦ t ⟧Term ⟦ ρ ⟧Env) ≡ ⟦ v ⟧Val
apply-sound _ v (closure ft ρ) a n s t feq aeq eq rewrite feq | aeq = eval-fun-sound (a • ρ) v n ft eq

eval-fun-sound ρ v n (term x) eq = eval-term-sound ρ v n x eq
eval-fun-sound ρ .(closure t ρ) n (abs t) refl = refl

eval-term-sound ρ v zero t ()
eval-term-sound ρ .(Op.⟦ x ⟧Var ρ) (ℕ.suc n) (var x) refl = ↦-sound ρ x
eval-term-sound ρ v (ℕ.suc n) (lett f x t) eq with apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n | inspect (apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ)) n
eval-term-sound ρ v (ℕ.suc n) (lett f x t) eq | Done fv | [ fveq ] rewrite apply-sound ρ fv (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n (var f) (var x) (↦-sound ρ f) (↦-sound ρ x) fveq = eval-term-sound (fv • ρ) v n t eq
eval-term-sound ρ v (ℕ.suc n) (lett f x t) () | Error | _
eval-term-sound ρ v (ℕ.suc n) (lett f x t) () | TimeOut | _
