module Thesis.SIRelBigStep.OpSem where

open import Data.Nat
open import Thesis.SIRelBigStep.Syntax public

data Val : Type → Set

import Base.Denotation.Environment
open Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

data Val where
  closure : ∀ {Γ σ τ} → (t : Term (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  natV : ∀ (n : ℕ) → Val nat
  pairV : ∀ {σ τ} → Val σ → Val τ → Val (pair σ τ)

eval-const : ∀ {τ} → Const τ → Val τ
eval-const (lit n) = natV n

eval : ∀ {Γ τ} (sv : SVal Γ τ) (ρ : ⟦ Γ ⟧Context) → Val τ
eval (var x) ρ = ⟦ x ⟧Var ρ
eval (abs t) ρ = closure t ρ
eval (cons sv1 sv2) ρ = pairV (eval sv1 ρ) (eval sv2 ρ)
eval (const c) ρ = eval-const c

eval-primitive : ∀ {σ τ} → Primitive (σ ⇒ τ) → Val σ → Val τ
eval-primitive succ (natV n) = natV (suc n)
eval-primitive add (pairV (natV n1) (natV n2)) = natV (n1 + n2)

-- Yann's idea.
data HasIdx : Set where
  true : HasIdx
  false : HasIdx
data Idx : HasIdx → Set where
  i' : ℕ → Idx true
  no : Idx false

i : {hasIdx : HasIdx} → ℕ → Idx hasIdx
i {false} j = no
i {true} j = i' j

module _ {hasIdx : HasIdx} where
  data _⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : ∀ {τ} → Term Γ τ → Idx hasIdx → Val τ → Set where
    val : ∀ {τ} (sv : SVal Γ τ) →
      ρ ⊢ val sv ↓[ i 1 ] eval sv ρ
    primapp : ∀ {σ τ} (p : Primitive (σ ⇒ τ)) (sv : SVal Γ σ) →
      ρ ⊢ primapp p sv ↓[ i 1 ] eval-primitive p (eval sv ρ)
    app : ∀ n {Γ′ σ τ ρ′} vtv {v} {vs : SVal Γ (σ ⇒ τ)} {vt : SVal Γ σ} {t : Term (σ • Γ′) τ} →
      ρ ⊢ val vs ↓[ i 1 ] closure t ρ′ →
      ρ ⊢ val vt ↓[ i 1 ] vtv →
      (vtv • ρ′) ⊢ t ↓[ i n ] v →
      ρ ⊢ app vs vt ↓[ i (suc (suc (suc n))) ] v
    lett :
      ∀ n1 n2 {σ τ} vsv {v} (s : Term Γ σ) (t : Term (σ • Γ) τ) →
      ρ ⊢ s ↓[ i n1 ] vsv →
      (vsv • ρ) ⊢ t ↓[ i n2 ] v →
      ρ ⊢ lett s t ↓[ i (suc n1 + n2) ] v
