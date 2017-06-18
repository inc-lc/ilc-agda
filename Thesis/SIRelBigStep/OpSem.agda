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
    abs : ∀ {σ τ} {t : Term (σ • Γ) τ} →
      ρ ⊢ val (abs t) ↓[ i 1 ] closure t ρ
    var : ∀ {τ} (x : Var Γ τ) →
      ρ ⊢ val (var x) ↓[ i 1 ] (⟦ x ⟧Var ρ)
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
    lit : ∀ n →
      ρ ⊢ const (lit n) ↓[ i 1 ] natV n
