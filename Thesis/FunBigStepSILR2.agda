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
open import Data.Nat -- using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
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
apply (closure t ρ) a n = eval t (a • ρ) n

eval (var x) ρ n = Done (⟦ x ⟧Var ρ) n
eval (abs t) ρ n = Done (closure t ρ) n
eval (const c) ρ n = evalConst c n
eval _ ρ zero = TimeOut
eval (app s t) ρ (suc n) = (eval s ρ >>= (λ sv → eval t ρ >>= λ tv → apply sv tv)) n

eval-const-mono : ∀ {τ} → (c : Const τ) → ∀ {v} n0 n1 → evalConst c n0 ≡ Done v n1 → evalConst c (suc n0) ≡ Done v (suc n1)
eval-const-mono (lit v) zero n1 ()
eval-const-mono (lit v) (suc n0) .n0 refl = refl

-- ARGH
{-# TERMINATING #-}
eval-mono : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) → ∀ v n0 n1 → eval t ρ n0 ≡ Done v n1 → eval t ρ (suc n0) ≡ Done v (suc n1)
eval-mono (const c) ρ v n0 n1 eq = eval-const-mono c n0 n1 eq
eval-mono (var x) ρ .(⟦ x ⟧Var ρ) n0 .n0 refl = refl
eval-mono (abs t) ρ .(closure t ρ) n0 .n0 refl = refl
eval-mono (app s t) ρ v zero n1 ()
eval-mono (app s t) ρ v (suc n0) n1 eq with eval s ρ n0 | inspect (eval s ρ) n0
eval-mono (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] with eval s ρ (suc n0) | eval-mono s ρ sv n0 n1 seq
eval-mono (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl with eval t ρ n1 | inspect (eval t ρ) n1
eval-mono (app s t) ρ v (suc n0) n3 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | Done tv n2 | [ teq ] with eval t ρ (suc n1) | eval-mono t ρ tv n1 n2 teq
eval-mono (app s t) ρ v (suc n0) n3 eq | Done (closure t₁ ρ₁) n1 | [ seq ] | .(Done (closure {Γ = _} {σ = _} {τ = _} t₁ ρ₁) (suc n1)) | refl | (Done tv n2) | [ teq ] | .(Done tv (suc n2)) | refl = eval-mono t₁ (tv • ρ₁) v n2 n3 eq
eval-mono (app s t) ρ v (suc n0) n2 () | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | Error | [ teq ]
eval-mono (app s t) ρ v (suc n0) n2 () | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | TimeOut | [ teq ]
eval-mono (app s t) ρ v (suc n0) n1 () | Error | [ seq ]
eval-mono (app s t) ρ v (suc n0) n1 () | TimeOut | [ seq ]

relT : ∀ {τ Γ1 Γ2} (t1 : Term Γ1 τ) (t2 : Term Γ2 τ) (ρ1 : ⟦ Γ1 ⟧Context) (ρ2 : ⟦ Γ2 ⟧Context) → ℕ → Set

relV : ∀ τ (v1 v2 : Val τ) → ℕ → Set
relV τ v1 v2 zero = ⊤
-- Seems the proof for abs would go through even if here we do not step down.
-- However, that only works as long as we use a typed language; not stepping
-- down here, in an untyped language, gives a non-well-founded definition.
relV nat v1 v2 (suc n) = v1 ≡ v2
relV (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) (suc n) =
  ∀ (k : ℕ) (k≤n : k ≤ n) v1 v2 →
  relV σ v1 v2 k →
  relT t1 t2 (v1 • ρ1) (v2 • ρ2) k

relρ : ∀ Γ (ρ1 ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
relρ ∅ ∅ ∅ n = ⊤
relρ (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = relV τ v1 v2 n × relρ Γ ρ1 ρ2 n

relT {τ} t1 t2 ρ1 ρ2 zero = ⊤
relT {τ} t1 t2 ρ1 ρ2 (suc n) =
  (v1 : Val τ) →
  ∀ n-j (n-j≤n : n-j ≤ n) →
  (eq : eval t1 ρ1 n ≡ Done v1 n-j) →
  Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] Σ[ n3 ∈ ℕ ] eval t2 ρ2 n2 ≡ Done v2 n3 × relV τ v1 v2 (suc n-j)

relV-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → relV τ v1 v2 n → relV τ v1 v2 m
relV-mono zero n m≤n τ v1 v2 vv = tt
relV-mono (suc m) (suc n) (s≤s m≤n) nat v1 v2 vv = vv
relV-mono (suc m) (suc n) (s≤s m≤n) (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) ff k k≤m = ff k (≤-trans k≤m m≤n)

relρ-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → relρ Γ ρ1 ρ2 n → relρ Γ ρ1 ρ2 m
relρ-mono m n m≤n ∅ ∅ ∅ tt = tt
relρ-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = relV-mono m n m≤n _ v1 v2 vv , relρ-mono m n m≤n Γ ρ1 ρ2 ρρ

fundamentalV : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT (var x) (var x) ρ1 ρ2 n
fundamentalV x zero ρ1 ρ2 ρρ = tt
fundamentalV this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 .n n-j≤n refl =  v2 , zero , zero , refl , vv
fundamentalV (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = fundamentalV  x (suc n) ρ1 ρ2 ρρ

-- relT (app s t) (app s t)

relV-apply : ∀ {σ τ Γ} (s : Term Γ (σ ⇒ τ)) t v1 ρ2 n-j →
  Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] Σ[ n3 ∈ ℕ ] eval (app s t) ρ2 n2 ≡ Done v2 n3 × relV τ v1 v2 (suc n-j)
relV-apply = {!!}

fundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT t t ρ1 ρ2 n
fundamental t zero ρ1 ρ2 ρρ = tt
fundamental (var x) (suc n) ρ1 ρ2 ρρ = fundamentalV x (suc n) ρ1 ρ2 ρρ
fundamental (const (lit v)) (suc zero) ρ1 ρ2 ρρ v1 n-j n-j≤n ()
fundamental (const (lit v)) (suc (suc n)) ρ1 ρ2 ρρ .(intV v) .n n-j≤n refl = intV v , suc zero , zero , refl , refl
fundamental (abs t) (suc n) ρ1 ρ2 ρρ .(closure t ρ1) .n n-j≤n refl =  closure t ρ2 , n , n , refl , (λ k k≤n v1 v2 vv → fundamental t k (v1 • ρ1) (v2 • ρ2) (vv , relρ-mono k (suc n) (≤-step k≤n) _ _ _ ρρ))
fundamental (app s t) (suc zero) ρ1 ρ2 ρρ v1 n-j n-j≤n ()
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq with eval s ρ1 n | inspect (eval s ρ1) n
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq | Done sv1 n1 | [ s1eq ] with eval t ρ1 n1 | inspect (eval t ρ1) n1
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq | Done (closure st1 sρ1) n1 | [ s1eq ] | Done tv1 n2 | [ t1eq ] with fundamental s _ ρ1 ρ2 ρρ (closure st1 sρ1) (suc n1) (s≤s {!!}) (eval-mono s ρ1 (closure st1 sρ1) n n1 s1eq) | fundamental t _ ρ1 ρ2 ρρ tv1 (suc n2) {!!} {!eval-mono t ρ1 tv1 n1 n2 t1eq!}
... | closure st2 sρ2 , sn3 , sn4 , s2eq , svv | tv2 , tn3 , tn4 , t2eq , tvv = {!!}
--
-- {!eval s ρ2 !}
-- fundamental s (suc (suc n)) ρ1 ρ2 ρρ (closure st1 sρ1) ? ?
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Done sv1 n1 | [ s1eq ] | Error | [ t1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Done sv1 n1 | [ s1eq ] | TimeOut | [ t1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Error | [ s1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | TimeOut | [ s1eq ]
