{-# OPTIONS --allow-unsolved-metas #-}
-- Step-indexed logical relations based on functional big-step semantics.
--
-- Goal for now: just prove the fundamental theorem of logical relations,
-- relating a term to itself in a different environments.
--
-- Because of closures, we need relations across different terms with different
-- contexts and environments.
--
-- This development is strongly inspired by Dargaye and Leroy (2010), "A
-- verified framework for higher-order uncurrying optimizations" (and a bit by
-- "Functional Big-Step Semantics"), though I deviate somewhere.
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
eval (const c) ρ (suc n) = evalConst c (suc n)
eval (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
eval (abs t) ρ (suc n) = Done (closure t ρ)
eval (app s t) ρ (suc n) with eval s ρ n | eval t ρ n
... | Done f | Done a = apply f a n
... | _ | _ = TimeOut

eval-const-mono : ∀ {τ} → (c : Const τ) → ∀ {v} n → evalConst c n ≡ Done v → evalConst c (suc n) ≡ Done v
eval-const-mono (lit v) n eq = eq
eval-mono : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) → ∀ v n → eval t ρ n ≡ Done v → eval t ρ (suc n) ≡ Done v
eval-mono t ρ v zero ()
eval-mono (const c) ρ v (suc n) eq = eval-const-mono c (suc n) eq
eval-mono (var x) ρ v (suc n) eq = eq
eval-mono (app s t) ρ v (suc n) eq with eval s ρ n | inspect (eval s ρ) n | eval t ρ n | inspect (eval t ρ) n
eval-mono (app s t) ρ v (suc n) eq | Done sv | [ seq ] | (Done tv) | [ teq ] with eval s ρ (suc n) | eval-mono s ρ sv n seq | eval t ρ (suc n) | eval-mono t ρ tv n teq
eval-mono (app s t) ρ v (suc n) eq | Done (closure ct cρ) | [ seq ] | (Done tv) | [ teq ] | .(Done (closure ct cρ)) | refl | .(Done tv) | refl = eval-mono ct (tv • cρ) _ n eq
eval-mono (app s t) ρ v (suc n) () | Done _ | [ seq ] | TimeOut | [ teq ]
eval-mono (app s t) ρ v (suc n) () | TimeOut | [ seq ] | tv | [ teq ]
-- = {!eval-mono s ρ (suc n)!}
eval-mono (abs t) ρ v (suc n) eq = eq

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

relV relV2 : ∀ τ (v1 v2 : Val τ) → ℕ → Set
relρ relρ2 : ∀ Γ (ρ1 ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
relρ ∅ ∅ ∅ n = ⊤
relρ (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = relV τ v1 v2 n × relρ Γ ρ1 ρ2 n

relρ2 ∅ ∅ ∅ n = ⊤
relρ2 (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = relV2 τ v1 v2 n × relρ2 Γ ρ1 ρ2 n

-- relT/relT2 doesn't ask input environments to be related, but the fundamental lemma
-- does do so.

-- Indexing not according to source. But I can't quite write the correct
-- indexing without changing the definitions a lot.
relT relT2 : ∀ {τ Γ1 Γ2} (t1 : Term Γ1 τ) (t2 : Term Γ2 τ) (ρ1 : ⟦ Γ1 ⟧Context) (ρ2 : ⟦ Γ2 ⟧Context) → ℕ → Set
relT {τ} t1 t2 ρ1 ρ2 n =
  (v1 : Val τ) →
  (eq : eval t1 ρ1 n ≡ Done v1) →
  Σ[ v2 ∈ Val τ ] (eval t2 ρ2 n ≡ Done v2 × relV τ v1 v2 n)

import Data.Fin as F
open F using (Fin; _ℕ-_)

-- This is closer to what's used in Dargaye and Leroy, but not the same.

relT2 {τ} t1 t2 ρ1 ρ2 n =
  (v1 : Val τ) →
  ∀ (j : Fin (suc n)) →
  (eq : eval t1 ρ1 (F.toℕ j) ≡ Done v1) →
  Σ[ v2 ∈ Val τ ] eval t2 ρ2 (F.toℕ j) ≡ Done v2 × relV2 τ v1 v2 (F.toℕ (n F.ℕ- j))

relV τ v1 v2 zero = ⊤
-- Seems the proof for abs would go through even if here we do not step down.
-- However, that only works as long as we use a typed language; not stepping
-- down here, in an untyped language, gives a non-well-founded definition.
relV (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) =
  ∀ (k : ℕ) (k≤n : k ≤ n) →
  ∀ v1 v2 → relV σ v1 v2 k → relT t1 t2 (v1 • ρ1) (v2 • ρ2) k
relV nat v1 v2 (suc n) = v1 ≡ v2

-- Copy of relV, but mentioning relT2
relV2 τ v1 v2 zero = ⊤
relV2 (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) =
  ∀ (k : ℕ) (k≤n : k ≤ n) →
  ∀ v1 v2 → relV2 σ v1 v2 k → relT2 t1 t2 (v1 • ρ1) (v2 • ρ2) k
relV2 nat v1 v2 (suc n) = v1 ≡ v2

open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

open import Data.Nat.Properties

relV2-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → relV2 τ v1 v2 n → relV2 τ v1 v2 m
relV2-mono zero n m≤n τ v1 v2 vv = tt
relV2-mono (suc m) zero () τ v1 v2 vv
relV2-mono (suc m) (suc n) m≤n nat v1 v2 vv = vv
relV2-mono (suc m) (suc n) (_≤_.s≤s m≤n) (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) vv k k≤m = vv k (DecTotalOrder.trans decTotalOrder k≤m m≤n)

relV-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → relV τ v1 v2 n → relV τ v1 v2 m
relV-mono zero n m≤n τ v1 v2 vv = tt
relV-mono (suc m) zero () τ v1 v2 vv
relV-mono (suc m) (suc n) m≤n nat v1 v2 vv = vv
relV-mono (suc m) (suc n) (_≤_.s≤s m≤n) (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) vv k k≤m = vv k (DecTotalOrder.trans decTotalOrder k≤m m≤n)

relρ-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → relρ Γ ρ1 ρ2 n → relρ Γ ρ1 ρ2 m
relρ-mono m n m≤n ∅ ∅ ∅ tt = tt
relρ-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = relV-mono m n m≤n _ v1 v2 vv , relρ-mono m n m≤n Γ ρ1 ρ2 ρρ

relρ2-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → relρ2 Γ ρ1 ρ2 n → relρ2 Γ ρ1 ρ2 m
relρ2-mono m n m≤n ∅ ∅ ∅ tt = tt
relρ2-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = relV2-mono m n m≤n _ v1 v2 vv , relρ2-mono m n m≤n Γ ρ1 ρ2 ρρ

-- relV-mono τ v1 v2 vv = tt
-- relV-mono nat v1 v2 (suc n) vv = vv
-- relV-mono (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) vv k k≤n = vv k ?

-- relV-mono : ∀ τ v1 v2 n → relV τ v1 v2 (suc n) → relV τ v1 v2 n
-- relV-mono τ v1 v2 zero vv = tt
-- relV-mono nat v1 v2 (suc n) vv = vv
-- relV-mono (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) vv k k≤n = vv k (≤-step k≤n)

-- True but useless.

-- relV-apply-go2 : ∀ {σ τ} sv1 sv2 tv1 tv2
--   n
--   (svv : relV (σ ⇒ τ) sv1 sv2 (suc (suc n)))
--   (tvv : relV σ tv1 tv2 (suc (suc n)))
--   v1 →
--   apply sv1 tv1 n ≡ Done v1 →
--   Σ[ v2 ∈ Val τ ] (apply sv2 tv2 n ≡ Done v2 × relV τ v1 v2 (suc n))
-- relV-apply-go2 (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 zero svv tvv v1 ()
-- relV-apply-go2 (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) svv tvv v1 eqv1
--   with svv (suc n) (≤-step ≤-refl) tv1 tv2 (relV-mono _ _ (≤-step (≤-step ≤-refl)) _ _ _ tvv) v1 eqv1
--   | svv (suc (suc n)) ≤-refl tv1 tv2 (relV-mono _ _ (≤-step ≤-refl) _ _ _ tvv) v1 (eval-mono st1 (tv1 • ρ1) v1 (suc n) eqv1)
-- relV-apply-go2 (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) svv tvv v1 eqv1 | v2' , eqv2' , final-v' | v2 , eqv2 , final-v with trans (sym (eval-mono st2 (tv2 • ρ2) v2' (suc n) eqv2')) eqv2
-- relV-apply-go2 (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) svv tvv v1 eqv1 | .v2 , eqv2' , final-v' | v2 , eqv2 , final-v | refl = v2 , eqv2' , final-v


relV-apply-go : ∀ {σ τ} sv1 sv2 tv1 tv2
  n
  (svv : relV (σ ⇒ τ) sv1 sv2 (suc n))
  (tvv : relV σ tv1 tv2 (suc n))
  v1 →
  apply sv1 tv1 n ≡ Done v1 →
  Σ[ v2 ∈ Val τ ] (apply sv2 tv2 n ≡ Done v2 × relV τ v1 v2 (suc n))
relV-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 zero svv tvv v1 ()
relV-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) svv tvv v1 eqv1
  with svv (suc n) ≤-refl tv1 tv2 ((relV-mono _ _ (≤-step ≤-refl) _ _ _ tvv)) v1 eqv1
relV-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) svv tvv v1 eqv1 | v2 , eqv2 , final-v = v2 , eqv2 , {!final-v!}

relV-apply : ∀ {σ τ sv1 sv2 tv1 tv2}
  n
  (svv : relV (σ ⇒ τ) sv1 sv2 (suc n))
  (tvv : relV σ tv1 tv2 (suc n))
  {v1} →
  apply sv1 tv1 n ≡ Done v1 →
  Σ[ v2 ∈ Val τ ] (apply sv2 tv2 n ≡ Done v2 × relV τ v1 v2 (suc n))
relV-apply n svv tvv eqv1 = relV-apply-go _ _ _ _ n svv tvv _ eqv1
--

-- -- fundamental lemma of logical relations.
-- fundamentalV : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT (var x) (var x) ρ1 ρ2 n
-- fundamentalV x zero _ _ _ _ ()
-- fundamentalV this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 refl = v2 , refl , vv
-- fundamentalV (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = fundamentalV x (suc n) ρ1 ρ2 ρρ

-- fundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT t t ρ1 ρ2 n

-- fundamental-aux : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 (suc n)) → (v1 : Val τ) →
--   eval t ρ1 n ≡ Done v1 →
--   Σ[ v2 ∈ Val τ ] (eval t ρ2 n ≡ Done v2 × eval t ρ2 (suc n) ≡ Done v2 × relV τ v1 v2 (suc n))
-- fundamental-aux s n ρ1 ρ2 ρρ sv1 seq1 with eval s ρ2 n | inspect (eval s ρ2) n | fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 seq1 | fundamental s (suc n) ρ1 ρ2 ρρ sv1 (eval-mono s ρ1 sv1 n seq1)
-- ... | Done sv2 | [ seq2 ] | (.sv2 , refl , svv) | (sv2' , sveq , svv') with trans (sym (eval-mono s ρ2 sv2 n seq2)) sveq
-- fundamental-aux s n ρ1 ρ2 ρρ sv1 seq1 | Done sv2 | [ seq2 ] | (.sv2 , refl , svv) | (.sv2 , sveq , svv') | refl = sv2 , refl , sveq , svv'
-- --
-- -- |
-- fundamental t zero ρ1 ρ2 ρρ v ()
-- -- XXX trivial case for constants.
-- fundamental (const (lit nv)) (suc n) ρ1 ρ2 ρρ .(intV nv) refl = intV nv , refl , refl
-- fundamental (var x) (suc n) ρ1 ρ2 ρρ v1 refl = fundamentalV x (suc n) ρ1 ρ2 ρρ (⟦ x ⟧Var ρ1) refl
-- fundamental (abs t) (suc n) ρ1 ρ2 ρρ (closure .t .ρ1) refl =
--   closure t ρ2 , refl , λ k k≤n v1 v2 vv → fundamental t k (v1 • ρ1) (v2 • ρ2) (vv , relρ-mono k _ (≤-step k≤n) _ _ _ ρρ)
-- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 with eval s ρ1 n | inspect (eval s ρ1) n | eval t ρ1 n | inspect (eval t ρ1) n
-- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | Done tv1 | [ teq1 ] with eval s ρ2 n | fundamental-aux s n ρ1 ρ2 ρρ sv1 seq1 | eval t ρ2 n | fundamental-aux t n ρ1 ρ2 ρρ tv1 teq1
-- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | (Done tv1) | [ teq1 ] | (Done sv2) | (.sv2 , refl , seq2' , svv') | (Done tv2) | (.tv2 , refl , teq2' , tvv') = relV-apply n svv' tvv' tρ1↓v1
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | Done tv1 | [ teq1 ] with eval s ρ2 n | inspect (eval s ρ2) n | fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 seq1 | fundamental s (suc n) ρ1 ρ2 ρρ sv1 (eval-mono s ρ1 sv1 n seq1)
-- -- ... | Done sv2 | [ seq2 ] | (.sv2 , refl , svv) | (sv2' , sveq , svv') with trans (sym (eval-mono s ρ2 sv2 n seq2)) sveq
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | (Done tv1) | [ teq1 ] | (Done sv2) | [ seq2 ] | (.sv2 , refl , svv) | (.sv2 , sveq , svv') | refl = {!!}
-- -- | fundamental t n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) tv1 teq1

-- -- fundamental {τ = τ} (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | Done tv1 | [ teq1 ] | Done sv2 | [ seq2 ] | Done tv2 | (.sv2 , refl , svv) | (.tv2 , refl , tvv) = relV-apply n svv tvv tρ1↓v1
-- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | Done sv1 | [ seq1 ] | TimeOut | [ teq1 ]
-- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | TimeOut | [ seq1 ] | tv1 | [ teq1 ]

-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ seq1 ] | Done tv1 | [ teq1 ] with eval s ρ2 n | inspect (eval s ρ2) n | eval t ρ2 n | fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 seq1
-- --... | sv2 | [ seq2 ] | tv2 | (sv2' , sρ2↓sv2 , svv) = ?


-- -- TODO: match sv2 before matching on fundamental s.
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | Done tv1 with eval s ρ2 n | inspect (eval s ρ2) n | eval t ρ2 n | fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 eq1
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | (Done sv2) | [ eq2 ] | (Done tv2) | [ teq1 ] | (sv2' , sρ2↓sv2 , svv) = {!!}
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | (Done sv2) | [ eq2 ] | TimeOut | [ teq1 ] | (sv2' , sρ2↓sv2 , svv) with fundamental t n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) tv1 {!teq1!}
-- -- ... | (tv2' , tρ2↓tv2 , tvv) = {!!}
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | TimeOut | [ eq2 ] | b | [ teq1 ] | (sv2' , () , svv)

-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | (Done sv2) | [ eq2 ] | (Done tv2) with fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 eq1
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | (Done sv2) | [ eq2 ] | (Done tv2) | (sv2' , sρ2↓sv2 , svv) = {!!}
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | (Done sv2) | [ eq2 ] | TimeOut = {!!}
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | (Done tv1) | TimeOut | [ eq2 ] | tv2 = {!!}
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | Done tv1 with fundamental s n ρ1 ρ2 (relρ-mono n _ (n≤1+n n) _ _ _ ρρ) sv1 eq1
-- -- fundamental {τ = τ} (app s t) (suc n) ρ1 ρ2 ρρ v1 tρ1↓v1 | Done sv1 | [ eq1 ] | Done tv1 | (sv2 , sρ2↓sv2 , svv) = v2 , {!!}
-- --   where
-- --     v2 : Val τ
-- --     v2 = {!!}
-- --     -- tρ2↓v2 : apply sv2 tv2 n ≡ Done v1
-- --     -- tρ2↓v2 = ?
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | Done sv | _ | TimeOut
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | TimeOut | _ | Done tv1
-- -- fundamental (app s t) (suc n) ρ1 ρ2 ρρ v1 () | TimeOut | _ | TimeOut

open import Data.Fin.Properties

ltn : ∀ n j → F.toℕ (n ℕ- j) ≤ suc n
ltn n Fin.zero rewrite to-from n = ≤-step ≤-refl
ltn zero (Fin.suc ())
ltn (suc n) (Fin.suc j) = ≤-step (ltn n j)

ltn2 : ∀ n j → F.toℕ (n ℕ- Fin.suc j) ≤ n
ltn2 zero ()
ltn2 (suc n) j = ltn n j

fundamentalV2 : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ2 Γ ρ1 ρ2 n) → relT2 (var x) (var x) ρ1 ρ2 n
fundamentalV2 x zero ρ1 ρ2 ρρ v1 Fin.zero ()
fundamentalV2 x zero ρ1 ρ2 ρρ v1 (Fin.suc ()) x₁
fundamentalV2 x (suc n) ρ1 ρ2 ρρ v1' Fin.zero ()
fundamentalV2 this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 (Fin.suc j) refl = v2 , refl , relV2-mono _ _ (ltn n j) _ v1 v2 vv
fundamentalV2 (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .(⟦ x ⟧Var ρ1) (Fin.suc j) refl = fundamentalV2 x (suc n) ρ1 ρ2 ρρ (⟦ x ⟧Var ρ1) (Fin.suc j) refl
-- fundamentalV2 this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) v1' Fin.zero ()
-- fundamentalV2 this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 (Fin.suc j) refl = {!!}
-- fundamentalV2 (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) v1' Fin.zero ()
-- fundamentalV2 (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .(⟦ x ⟧Var ρ1) (Fin.suc j) refl = fundamentalV2 x (suc n) ρ1 ρ2 ρρ (⟦ x ⟧Var ρ1) (Fin.suc j) refl
-- --

-- fundamentalV2 x zero _ _ _ _ ()
-- fundamentalV2 this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 refl = v2 , refl , vv
-- fundamentalV2 (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = fundamentalV x (suc n) ρ1 ρ2 ρρ

relV-nat-refl : ∀ nv n → relV2 nat nv nv n
relV-nat-refl (intV nv) zero = tt
relV-nat-refl (intV nv) (suc n) = refl


relV2-apply-go : ∀ {σ τ} sv1 sv2 tv1 tv2
  n j
  (svv : relV2 (σ ⇒ τ) sv1 sv2 (F.toℕ (n ℕ- Fin.suc j)))
  (tvv : relV2 σ tv1 tv2 (F.toℕ (n ℕ- Fin.suc j)))
  v1 →
  (eqv1 : apply sv1 tv1 (suc (F.toℕ j)) ≡ Done v1) →
  Σ[ v2 ∈ Val τ ] (apply sv2 tv2 (suc (F.toℕ j)) ≡ Done v2 × relV2 τ v1 v2 (F.toℕ (n ℕ- Fin.suc j)))
relV2-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc zero) Fin.zero tt tt v1 eqv1 = {!!}
relV2-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc (suc n)) Fin.zero svv tvv v1 eqv1 = {!!}
relV2-apply-go (closure st1 ρ1) (closure st2 ρ2) tv1 tv2 (suc n) (Fin.suc j) svv tvv v1 eqv1 = {!!}

relV2-apply : ∀ {σ τ sv1 sv2 tv1 tv2}
  n j
  (svv : relV2 (σ ⇒ τ) sv1 sv2 (F.toℕ (n ℕ- Fin.suc j)))
  (tvv : relV2 σ tv1 tv2 (F.toℕ (n ℕ- Fin.suc j)))
  {v1} →
  apply sv1 tv1 (suc (F.toℕ j)) ≡ Done v1 →
  Σ[ v2 ∈ Val τ ] (apply sv2 tv2 (suc (F.toℕ j)) ≡ Done v2 × relV2 τ v1 v2 (F.toℕ (n ℕ- Fin.suc j)))
relV2-apply n j svv tvv eqv1 = relV2-apply-go _ _ _ _ n j svv tvv _ eqv1

fundamental2 : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ2 Γ ρ1 ρ2 n) → relT2 t t ρ1 ρ2 n
fundamental2 t n ρ1 ρ2 ρρ v1 Fin.zero ()
fundamental2 (const (lit nv)) n ρ1 ρ2 ρρ .(intV nv) (Fin.suc j) refl = intV nv , refl , relV-nat-refl (intV nv) (F.toℕ (n ℕ- Fin.suc j))
fundamental2 (var x) n ρ1 ρ2 ρρ .(⟦ x ⟧Var ρ1) (Fin.suc j) refl = fundamentalV2 x n ρ1 ρ2 ρρ (⟦ x ⟧Var ρ1) (Fin.suc j) refl
fundamental2 (abs t) n ρ1 ρ2 ρρ .(closure t ρ1) (Fin.suc j) refl = closure t ρ2 , refl , res-valid (F.toℕ (n ℕ- Fin.suc j)) (ltn2 n j)
  -- foo (F.toℕ (n ℕ- Fin.suc j))
  where
    res-valid : ∀ nj → nj ≤ n → relV2 _ (closure t ρ1) (closure t ρ2) nj
    res-valid zero nj≤n = tt
    res-valid (suc nj) nj≤n k k≤nj v1 v2 vv v3 Fin.zero ()
    res-valid (suc nj) nj≤n k k≤nj v1 v2 vv v3 (Fin.suc j₁) eq = fundamental2 t k (v1 • ρ1) (v2 • ρ2) (vv , relρ2-mono _ _ (≤-trans k≤nj (≤-trans (≤-step ≤-refl) nj≤n)) _ _ _ ρρ) v3 (Fin.suc j₁) eq

    -- foo : relV2 _ (closure t ρ1) (closure t ρ2) (F.toℕ (n ℕ- Fin.suc j))
    -- foo with (F.toℕ (n ℕ- Fin.suc j))
    -- foo | zero = tt
    -- foo | (suc nj) = λ k k≤nj v1 v2 vv v3 j₁ eq → {!!}

    -- λ k k≤nj v1 v2 vv v3 j₁ eq →
    -- fundamental2 t k (v1 • ρ1) (v2 • ρ2) (vv , relρ-mono k _ (≤-step k≤nj) _ _ _ ρρ)

    -- foo | zero = ?
    -- foo | (suc nj) k k≤nj v1 v2 vv = {!!}
fundamental2 (app s t) (suc _) ρ1 ρ2 ρρ v1 (Fin.suc Fin.zero) ()
fundamental2 (app s t) (suc _) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) appst-ρ1↓v1 with eval s ρ1 (suc (F.toℕ j)) | inspect (eval s ρ1) (suc (F.toℕ j))
fundamental2 (app s t) (suc _) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) appst-ρ1↓v1 | Done sv1 | [ sρ1↓sv1 ] with eval t ρ1 (suc (F.toℕ j)) | inspect (eval t ρ1) (suc (F.toℕ j))
fundamental2 (app s t) (suc n) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) appst-ρ1↓v1 | Done sv1 | [ sρ1↓sv1 ] | Done tv1 | [ tρ1↓tv1 ] with eval s ρ2 (suc (F.toℕ j)) | fundamental2 s n ρ1 ρ2 (relρ2-mono n (suc n) (≤-step ≤-refl) _ _ _ ρρ) sv1 (Fin.suc j) sρ1↓sv1
fundamental2 (app s t) (suc n) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) appst-ρ1↓v1 | Done sv1 | [ sρ1↓sv1 ] | (Done tv1) | [ tρ1↓tv1 ] | .(Done sv2) | (sv2 , refl , svv) with
  eval t ρ2 (suc (F.toℕ j)) | fundamental2 t n ρ1 ρ2 (relρ2-mono n (suc n) (≤-step ≤-refl) _ _ _ ρρ) tv1 (Fin.suc j) tρ1↓tv1
... | .(Done tv2) | (tv2 , refl , tvv) = relV2-apply n j svv tvv appst-ρ1↓v1
fundamental2 (app s t) (suc _) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) () | Done sv1 | [ sρ1↓sv1 ] | TimeOut | [ tρ1↓tv1 ]
fundamental2 (app s t) (suc _) ρ1 ρ2 ρρ v1 (Fin.suc (Fin.suc j)) () | TimeOut | [ sρ1↓sv1 ]
