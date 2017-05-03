-- Step-indexed logical relations based on functional big-step semantics.
--
-- Goal for now: just prove the fundamental theorem of logical relations,
-- relating a term to itself in a different environments.
--
-- Because of closures, we need relations across different terms with different
-- contexts and environments.
--
-- This development is strongly inspired by "A verified framework for
-- higher-order uncurrying optimizations" (and a bit by "Functional Big-Step
-- Semantics"), though I deviate somewhere.
module Thesis.FunBigStepSILR where

open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)

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
-- step-indexing with a fuel value, following "Type Soundness Proofs with
-- Definitional Interpreters". Since we focus for now on STLC, unlike that
-- paper, we can avoid error values by keeping types.
--
-- One could drop types and add error values, to reproduce what they do.

data ErrVal (τ : Type) : Set where
  Done : (v : Val τ) → ErrVal τ
  TimeOut : ErrVal τ

Res : Type → Set
Res τ = ℕ → ErrVal τ

evalConst : ∀ {τ} → Const τ → Res τ
evalConst (lit v) n = Done (intV v)

eval : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure t ρ) a n = eval t (a • ρ) n

eval t ρ zero = TimeOut
eval (const c) ρ (suc n) = evalConst c n
eval (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
eval (abs t) ρ (suc n) = Done (closure t ρ)
eval (app s t) ρ (suc n) with eval s ρ n | eval t ρ n
... | Done f | Done a = apply f a n
... | _ | _ = TimeOut

-- Can we prove eval sound wrt. our reference denotational semantics? Yes! Very
-- cool! (Commented out until I paste that semantics here.)
-- eval-sound : ∀ {Γ τ} ρ v n (t : Term Γ τ) →
--   eval t ρ n ≡ Done v →
--   ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

-- apply-sound : ∀ {Γ σ τ} ρ v f a n (s : Term Γ (σ ⇒ τ)) t →
--   ⟦ s ⟧Term ⟦ ρ ⟧Env ≡ ⟦ f ⟧Val →
--   ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ a ⟧Val →
--   apply f a n ≡ Done v →
--   ⟦ s ⟧Term ⟦ ρ ⟧Env (⟦ t ⟧Term ⟦ ρ ⟧Env) ≡ ⟦ v ⟧Val
-- apply-sound _ v (closure ft ρ) a n s t feq aeq eq rewrite feq | aeq = eval-sound (a • ρ) v n ft eq

-- eval-sound ρ v zero t ()
-- eval-sound ρ v (ℕ.suc n) (const c) eq = {!!}
-- eval-sound ρ v (ℕ.suc n) (var x) refl = ↦-sound ρ x
-- eval-sound ρ v (ℕ.suc n) (abs t) refl = refl
-- eval-sound ρ v (ℕ.suc n) (app s t) eq with eval s ρ n | inspect (eval s ρ) n | eval t ρ n | inspect (eval t ρ) n
-- eval-sound ρ v (ℕ.suc n) (app s t) eq | Done f | [ feq ] | Done a | [ aeq ] =
--   let feq = eval-sound ρ f n s feq; aeq = eval-sound ρ a n t aeq in apply-sound ρ v f a n s t feq aeq eq
-- eval-sound ρ v (ℕ.suc n) (app s t) () | Done f | _ | TimeOut | _
-- eval-sound ρ v (ℕ.suc n) (app s t) () | TimeOut | _ | _ | _
-- -- eval-sound n (const c) eq = {!!}
-- -- eval-sound n (var x) eq = {!!}
-- -- eval-sound n (app s t) eq = {!!} -- with eval s ρ n
-- -- eval-sound n (abs t) eq = {!!}
-- -- eval-sound n (const c) eq = {!!}
-- -- eval-sound n (var x) eq = {!!}
-- -- eval-sound n (app s t) eq = {!!} -- with eval s ρ n
-- -- eval-sound n (abs t) eq = {!!}

relV : ∀ τ (v1 v2 : Val τ) → ℕ → Set
relρ : ∀ Γ (ρ1 ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
relρ ∅ ∅ ∅ n = ⊤
relρ (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = relV τ v1 v2 n × relρ Γ ρ1 ρ2 n

-- Indexing not according to source. But I can't quite write the correct
-- indexing without changing the definitions a lot.
relT : ∀ {τ Γ1 Γ2} (t1 : Term Γ1 τ) (t2 : Term Γ2 τ) (ρ1 : ⟦ Γ1 ⟧Context) (ρ2 : ⟦ Γ2 ⟧Context) → ℕ → Set
relT {τ} t1 t2 ρ1 ρ2 n =
  (v1 : Val τ) →
  eval t1 ρ1 n ≡ Done v1 →
  Σ[ v2 ∈ Val τ ] (eval t2 ρ2 n ≡ Done v2 × relV τ v1 v2 n)

relV τ v1 v2 zero = ⊤
relV (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) =
  ∀ (k : ℕ) (k≤n : k ≤ n) →
  ∀ v1 v2 → relV σ v1 v2 k → relT t1 t2 (v1 • ρ1) (v2 • ρ2) k
relV nat v1 v2 (suc n) = v1 ≡ v2

open import Data.Nat.Properties

relV-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → relV τ v1 v2 n → relV τ v1 v2 m
relV-mono zero n m≤n τ v1 v2 vv = tt
relV-mono (suc m) zero () τ v1 v2 vv
relV-mono (suc m) (suc n) m≤n nat v1 v2 vv = vv
relV-mono (suc m) (suc n) (_≤_.s≤s m≤n) (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) vv k k≤m = vv k (DecTotalOrder.trans decTotalOrder k≤m m≤n)

relρ-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → relρ Γ ρ1 ρ2 n → relρ Γ ρ1 ρ2 m
relρ-mono m n m≤n ∅ ∅ ∅ tt = tt
relρ-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = relV-mono m n m≤n _ v1 v2 vv , relρ-mono m n m≤n Γ ρ1 ρ2 ρρ

-- relV-mono τ v1 v2 vv = tt
-- relV-mono nat v1 v2 (suc n) vv = vv
-- relV-mono (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) vv k k≤n = vv k ?

-- relV-mono : ∀ τ v1 v2 n → relV τ v1 v2 (suc n) → relV τ v1 v2 n
-- relV-mono τ v1 v2 zero vv = tt
-- relV-mono nat v1 v2 (suc n) vv = vv
-- relV-mono (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) vv k k≤n = vv k (≤-step k≤n)

-- fundamental lemma of logical relations.
fundamentalV : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT (var x) (var x) ρ1 ρ2 n
fundamentalV x zero _ _ _ _ ()
fundamentalV this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 refl = v2 , refl , vv
fundamentalV (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = fundamentalV x (suc n) ρ1 ρ2 ρρ

fundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT t t ρ1 ρ2 n
fundamental t zero ρ1 ρ2 ρρ v ()
-- XXX trivial case for constants.
fundamental (const (lit nv)) (suc n) ρ1 ρ2 ρρ .(intV nv) refl = intV nv , refl , refl
fundamental (var x) (suc n) ρ1 ρ2 ρρ v1 refl = fundamentalV x (suc n) ρ1 ρ2 ρρ (⟦ x ⟧Var ρ1) refl
fundamental (abs t) (suc n) ρ1 ρ2 ρρ (closure .t .ρ1) refl =
  closure t ρ2 , refl , λ k k≤n v1 v2 vv → fundamental t k (v1 • ρ1) (v2 • ρ2) (vv , relρ-mono k _ (≤-step k≤n) _ _ _ ρρ)
fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 with eval s ρ1 n | inspect (eval s ρ1) n | eval t ρ1 n
-- TODO: match sv2 before matching on fundamental s.
fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq ] | Done tv1 with fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 eq
fundamental {τ = τ} (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq ] | Done tv1 | (sv2 , sρ2↓sv2 , svv) = v2 , {!!}
  where
    v2 : Val τ
    v2 = {!!}
    -- tρ2↓v2 : apply sv2 tv2 n ≡ Done v1
    -- tρ2↓v2 = ?
fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | Done sv | _ | TimeOut
fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | TimeOut | _ | Done tv1
fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | TimeOut | _ | TimeOut
