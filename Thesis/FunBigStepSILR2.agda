{-# OPTIONS --allow-unsolved-metas #-}
-- Step-indexed logical relations based on functional big-step semantics.
--
-- Goal for now: just prove the fundamental theorem of logical relations,
-- relating a term to itself in a different environments.
--
-- Because of closures, we need relations across different terms with different
-- contexts and environments.
--
-- This development is strongly inspired by "Imperative self-adjusting
-- computation", POPL'08, in preference to Dargaye and Leroy (2010), "A verified
-- framework for higher-order uncurrying optimizations", but I deviate
-- somewhere, especially to try following "Functional Big-Step Semantics"),
-- though I deviate somewhere.

module Thesis.FunBigStepSILR2 where

open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
open import Data.Nat.Properties
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  nat : Type

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ nat ⟧Type = ℕ

open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public

data Const : (τ : Type) → Set where
  lit : ℕ → Const nat
  -- succ : Const (int ⇒ int)

data Term (Γ : Context) :
  (τ : Type) → Set where
  -- constants aka. primitives
  const : ∀ {τ} →
    (c : Const τ) →
    Term Γ τ
  var : ∀ {τ} →
    (x : Var Γ τ) →
    Term Γ τ
  app : ∀ {σ τ}
    (s : Term Γ (σ ⇒ τ)) →
    (t : Term Γ σ) →
    Term Γ τ
  -- we use de Bruijn indices, so we don't need binding occurrences.
  abs : ∀ {σ τ}
    (t : Term (σ • Γ) τ) →
    Term Γ (σ ⇒ τ)

data Val : Type → Set
open import Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

data Val where
  closure : ∀ {Γ σ τ} → (t : Term (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  intV : ∀ (n : ℕ) → Val nat

import Base.Denotation.Environment
-- Den stands for Denotational semantics.
module Den = Base.Denotation.Environment Type ⟦_⟧Type

--
-- Functional big-step semantics
--

-- Termination is far from obvious to Agda once we use closures. So we use
-- step-indexing with a fuel value.
-- Since we focus for now on STLC, unlike that
-- paper, we can avoid error values by keeping types.
--
-- One could drop types and add error values instead.

data ErrVal (τ : Type) : Set where
  Done : (v : Val τ) → (n1 : ℕ) → ErrVal τ
  Error : ErrVal τ
  TimeOut : ErrVal τ

Res : Type → Set
Res τ = (n : ℕ) → ErrVal τ

_>>=_ : ∀ {σ τ} → Res σ → (Val σ → Res τ) → Res τ
(s >>= t) n0 with s n0
... | Done v n1 = t v n1
... | Error = Error
... | TimeOut = TimeOut

evalConst : ∀ {τ} → Const τ → Res τ
evalConst (lit v) zero = TimeOut
evalConst (lit v) (suc n) = Done (intV v) n

{-# TERMINATING #-}
eval : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure t ρ) a (suc n) = eval t (a • ρ) n
apply (closure t ρ) a zero = TimeOut

eval (var x) ρ n = Done (⟦ x ⟧Var ρ) n
eval (abs t) ρ n = Done (closure t ρ) n
eval (const c) ρ n = evalConst c n
eval _ ρ zero = TimeOut
eval (app s t) ρ = eval s ρ >>= (λ sv → eval t ρ >>= λ tv → apply sv tv)
