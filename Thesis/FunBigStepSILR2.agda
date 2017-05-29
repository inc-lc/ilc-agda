-- Step-indexed logical relations based on functional big-step semantics.
--
-- Goal for now: just prove the fundamental theorem of logical relations,
-- relating a term to itself in a different environments.
--
-- But to betray the eventual goal, I can also relate integer values with a
-- change in the relation witness. That was a completely local change. But that
-- might also be because we only have few primitives.
--
-- Because of closures, we need relations across different terms with different
-- contexts and environments.
--
-- This development is strongly inspired by "Imperative self-adjusting
-- computation" (ISAC below), POPL'08, in preference to Dargaye and Leroy (2010), "A verified
-- framework for higher-order uncurrying optimizations", but I deviate
-- somewhere, especially to try following "Functional Big-Step Semantics"),
-- though I deviate somewhere.

-- CHEATS:
-- "Fuctional big-step semantics" requires an external termination proof for the
-- semantics. There it is also mechanized, here it isn't. Worse, the same
-- termination problem affects some lemmas about the semantics.

module Thesis.FunBigStepSILR2 where

open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat -- using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
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

-- WARNING: ISAC's big-step semantics produces a step count as "output". But
-- that would not help Agda establish termination. That's only a problem for a
-- functional big-step semantics, not for a relational semantics.
--
-- So, instead, I tried to use a sort of writer monad: the interpreter gets fuel
-- and returns the remaining fuel. That's the same trick as in "functional
-- big-step semantics". That *makes* the function terminating, even though Agda
-- cannot see this because it does not know that the returned fuel is no bigger.

-- Since we focus for now on STLC, unlike that
-- paper, we could avoid error values because we keep types.
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
evalConst (lit v) n = Done (intV v) n

{-# TERMINATING #-}
eval : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure t ρ) a n = eval t (a • ρ) n

eval (var x) ρ n = Done (⟦ x ⟧Var ρ) n
eval (abs t) ρ n = Done (closure t ρ) n
eval (const c) ρ n = evalConst c n
eval _ ρ zero = TimeOut
eval (app s t) ρ (suc n) = (eval s ρ >>= (λ sv → eval t ρ >>= λ tv → apply sv tv)) n

eval-const-dec : ∀ {τ} → (c : Const τ) → ∀ {v} n0 n1 → evalConst c n0 ≡ Done v n1 →  n1 ≤ n0
eval-const-dec (lit v) n0 .n0 refl = ≤-refl

{-# TERMINATING #-}
eval-dec : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ v n0 n1 → eval t ρ n0 ≡ Done v n1 → n1 ≤ n0
eval-dec (const c) ρ v n0 n1 eq = eval-const-dec c n0 n1 eq
eval-dec (var x) ρ .(⟦ x ⟧Var ρ) n0 .n0 refl = ≤-refl
eval-dec (abs t) ρ .(closure t ρ) n0 .n0 refl = ≤-refl
eval-dec (app s t) ρ v zero n1 ()
eval-dec (app s t) ρ v (suc n0) n3 eq  with eval s ρ n0 | inspect (eval s ρ) n0
eval-dec (app s t) ρ v (suc n0) n3 eq | Done sv sn1 | [ seq ] with eval t ρ sn1 | inspect (eval t ρ) sn1
eval-dec (app s t) ρ v (suc n0) n3 eq | Done sv@(closure st sρ) sn1 | [ seq ] | (Done tv tn2) | [ teq ] = ≤-step (≤-trans (≤-trans (eval-dec st _ _ _ _ eq) (eval-dec t _ _ _ _ teq)) (eval-dec s _ _ _ _ seq))
eval-dec (app s t) ρ v (suc n0) n3 () | Done sv sn1 | [ seq ] | Error | [ teq ]
eval-dec (app s t) ρ v (suc n0) n3 () | Done sv sn1 | [ seq ] | TimeOut | [ teq ]
eval-dec (app s t) ρ v (suc n0) n3 () | Error | [ seq ]
eval-dec (app s t) ρ v (suc n0) n3 () | TimeOut | [ seq ]

eval-const-mono : ∀ {τ} → (c : Const τ) → ∀ {v} n0 n1 → evalConst c n0 ≡ Done v n1 → evalConst c (suc n0) ≡ Done v (suc n1)
eval-const-mono (lit v) n0 .n0 refl = refl

-- ARGH
{-# TERMINATING #-}
eval-mono : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ v n0 n1 → eval t ρ n0 ≡ Done v n1 → eval t ρ (suc n0) ≡ Done v (suc n1)
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

eval-adjust-plus : ∀ d {Γ τ} → (t : Term Γ τ) → ∀ ρ v n0 n1 → eval t ρ n0 ≡ Done v n1 → eval t ρ (d + n0) ≡ Done v (d + n1)
eval-adjust-plus zero t ρ v n0 n1 eq = eq
eval-adjust-plus (suc d) t ρ v n0 n1 eq = eval-mono t ρ v (d + n0) (d + n1) (eval-adjust-plus d t ρ v n0 n1 eq)

eval-const-strengthen : ∀ {τ} → (c : Const τ) → ∀ {v} n0 n1 → evalConst c (suc n0) ≡ Done v (suc n1) → evalConst c n0 ≡ Done v n1
eval-const-strengthen (lit v) n0 .n0 refl = refl

-- I started trying to prove eval-strengthen, which I appeal to informally
-- below, but I gave up. I still guess the lemma is true but proving it looks
-- too painful to bother.

-- Without this lemma, I can't fully prove that this logical relation is
-- equivalent to the original one.
-- But this one works (well, at least up to the fundamental theorem, haven't
-- attempted other lemmas), so it should be good enough.

-- eval-mono-err : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ n → eval t ρ n ≡ Error → eval t ρ (suc n) ≡ Error
-- eval-mono-err (const (lit x)) ρ zero eq = {!!}
-- eval-mono-err (const (lit x)) ρ (suc n) eq = {!!}
-- eval-mono-err (var x) ρ n eq = {!!}
-- eval-mono-err (app t t₁) ρ n eq = {!!}
-- eval-mono-err (abs t) ρ n eq = {!!}

-- -- eval t ρ (suc n0) ≡ Done v (suc n1) → eval t ρ n0 ≡ Done v n
-- eval-aux : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ n → (Σ[ res0 ∈ ErrVal τ ] eval t ρ n ≡ res0) × (Σ[ resS ∈ ErrVal τ ] eval t ρ n ≡ resS)
-- eval-aux t ρ n with
--   eval t ρ n | inspect (eval t ρ) n |
--   eval t ρ (suc n) | inspect (eval t ρ) (suc n)
-- eval-aux t ρ n | res0 | [ eq0 ] | (Done v1 n1) | [ eq1 ] = {!!}
-- eval-aux t ρ n | res0 | [ eq0 ] | Error | [ eq1 ] = {!!}
-- eval-aux t ρ n | Done v n1 | [ eq0 ] | TimeOut | [ eq1 ] = {!!}
-- eval-aux t ρ n | Error | [ eq0 ] | TimeOut | [ eq1 ] = {!!}
-- eval-aux t ρ n | TimeOut | [ eq0 ] | TimeOut | [ eq1 ] = (TimeOut , refl) , (TimeOut , refl)

-- {-# TERMINATING #-}
-- eval-strengthen : ∀ {Γ τ} → (t : Term Γ τ) → ∀ ρ v n0 n1 → eval t ρ (suc n0) ≡ Done v (suc n1) → eval t ρ n0 ≡ Done v n1
-- eval-strengthen (const c) ρ v n0 n1 eq = eval-const-strengthen c n0 n1 eq
-- eval-strengthen (var x) ρ .(⟦ x ⟧Var ρ) n0 .n0 refl = refl
-- eval-strengthen (abs t) ρ .(closure t ρ) n0 .n0 refl = refl
-- eval-strengthen (app s t) ρ v zero n1 eq with eval s ρ 0 | inspect (eval s ρ) 0
-- eval-strengthen (app s t) ρ v zero n1 eq | Done sv sn1 | [ seq ] with eval-dec s ρ sv 0 sn1 seq
-- eval-strengthen (app s t) ρ v zero n1 eq | Done sv .0 | [ seq ] | z≤n with eval t ρ 0 | inspect (eval t ρ) 0
-- eval-strengthen (app s t) ρ v zero n1 eq | Done sv _ | [ seq ] | z≤n | Done tv tn1 | [ teq ]  with eval-dec t ρ tv 0 tn1 teq
-- eval-strengthen (app s t) ρ v zero n1 eq | Done (closure st sρ) _ | [ seq ] | z≤n | (Done tv .0) | [ teq ] | z≤n with eval-dec st _ v 0 (suc n1) eq
-- eval-strengthen (app s t) ρ v zero n1 eq | Done (closure st sρ) _ | [ seq ] | z≤n | (Done tv _) | [ teq ] | z≤n | ()
-- eval-strengthen (app s t) ρ v zero n1 () | Done sv _ | [ seq ] | z≤n | Error | [ teq ]
-- eval-strengthen (app s t) ρ v zero n1 () | Done sv _ | [ seq ] | z≤n | TimeOut | [ teq ]
-- eval-strengthen (app s t) ρ v zero n1 () | Error | [ seq ]
-- eval-strengthen (app s t) ρ v zero n1 () | TimeOut | [ seq ]
-- -- eval-dec s ρ
-- --  {!eval-dec s ρ ? (suc zero) (suc n1) !}
-- -- eval-strengthen (app s t) ρ v (suc n0) n1 eq with eval s ρ (suc n0) | inspect (eval s ρ) (suc n0)
-- -- eval-strengthen (app s t) ρ v₁ (suc n0) n2 eq | Done sv n1 | [ seq ] with eval s ρ n0 = {!eval-strengthen s ρ v n0 n1 seq !}
-- -- eval-strengthen (app s t) ρ v (suc n0) n1 () | Error | [ seq ]
-- -- eval-strengthen (app s t) ρ v (suc n0) n1 () | TimeOut | [ seq ]
-- eval-strengthen (app s t) ρ v (suc n0) n1 eq with eval s ρ n0 | inspect (eval s ρ) n0
-- eval-strengthen (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] with eval s ρ (suc n0) | eval-mono s ρ sv n0 n1 seq
-- eval-strengthen (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl with eval t ρ n1 | inspect (eval t ρ) n1
-- eval-strengthen (app s t) ρ v (suc n0) n3 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | Done tv n2 | [ teq ] with eval t ρ (suc n1) | eval-mono t ρ tv n1 n2 teq
-- eval-strengthen (app s t) ρ v (suc n0) n3 eq | Done (closure t₁ ρ₁) n1 | [ seq ] | .(Done (closure {Γ = _} {σ = _} {τ = _} t₁ ρ₁) (suc n1)) | refl | (Done tv n2) | [ teq ] | .(Done tv (suc n2)) | refl = eval-strengthen t₁ (tv • ρ₁) v n2 n3 eq
-- eval-strengthen (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | Error | [ teq ] = {!!}
-- eval-strengthen (app s t) ρ v (suc n0) n2 eq | Done sv n1 | [ seq ] | .(Done sv (suc n1)) | refl | TimeOut | [ teq ] = {!!}
-- eval-strengthen (app s t) ρ v (suc n0) n1 eq | Error | [ seq ] = {!!}
-- eval-strengthen (app s t) ρ v (suc n0) n1 eq | TimeOut | [ seq ] = {!!}

-- eval-adjust-minus : ∀ d {Γ τ} → (t : Term Γ τ) → ∀ {ρ v} n0 n1 → eval t ρ (d + n0) ≡ Done v (d + n1) → eval t ρ n0 ≡ Done v n1
-- eval-adjust-minus zero t n0 n1 eq = eq
-- eval-adjust-minus (suc d) t n0 n1 eq = eval-adjust-minus d t n0 n1 (eval-strengthen t _ _ (d + n0) (d + n1) eq)

import Data.Integer as I
open I using (ℤ)
mutual
  -- This is not the same definition of relT, but it is equivalent.
  relT : ∀ {τ Γ1 Γ2} (t1 : Term Γ1 τ) (t2 : Term Γ2 τ) (ρ1 : ⟦ Γ1 ⟧Context) (ρ2 : ⟦ Γ2 ⟧Context) → ℕ → Set
  -- This equation is a lemma in the original definition.
  relT {τ} t1 t2 ρ1 ρ2 zero = ⊤
  -- To compare this definition, note that the original k is suc n here.
  relT {τ} t1 t2 ρ1 ρ2 (suc n) =
    (v1 : Val τ) →
    -- Originally we have 0 ≤ j < k, so j < suc n, so k - j = suc n - j.
    -- It follows that 0 < k - j ≤ k, hence suc n - j ≤ suc n, or n - j ≤ n.
    -- Here, instead of binding j we bind n-j = n - j, require n - j ≤ n, and
    -- use suc n-j instead of k - j.
    ∀ n-j (n-j≤n : n-j ≤ n) →
    -- The next assumption is important. This still says that evaluation consumes j steps.
    -- Since j ≤ n, it is OK to start evaluation with n steps.
    -- Starting with (suc n) and getting suc n-j is equivalent, per eval-mono
    -- and eval-strengthen. But in practice this version is easier to use.
    (eq : eval t1 ρ1 n ≡ Done v1 n-j) →
    Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] eval t2 ρ2 n2 ≡ Done v2 0 × relV τ v1 v2 (suc n-j)
    -- Here, computing t2 is allowed to take an unbounded number of steps. Having to write a number at all is annoying.

  relV : ∀ τ (v1 v2 : Val τ) → ℕ → Set
  -- Show the proof still goes through if we relate clearly different values by
  -- inserting changes in the relation.
  -- There's no syntax to produce such changes, but you can add changes to the
  -- environment.
  relV nat (intV v1) (intV v2) n = Σ[ dv ∈ ℤ ] dv I.+ (I.+ v1) ≡ (I.+ v2)
  relV (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) n =
    ∀ (k : ℕ) (k≤n : k < n) v1 v2 →
    relV σ v1 v2 k →
    relT t1 t2 (v1 • ρ1) (v2 • ρ2) k
  -- Above, in the conclusion, I'm not relating app (closure t1 ρ1) v1 with app
  -- (closure t2 ρ2) v2 (or some encoding of that that actually works), but the
  -- result of taking a step from that configuration. That is important, because
  -- both Pitts' "Step-Indexed Biorthogonality: a Tutorial Example" and
  -- "Imperative Self-Adjusting Computation" do the same thing (and point out it's
  -- important).

  -- Relate λ x → 0 and λ x → 1 at any step count.
  example1 : ∀ n → relV (nat ⇒ nat) (closure (const (lit 0)) ∅) (closure (const (lit 1)) ∅) n
  example1 n zero k≤n v1 v2 x = tt
  example1 n (suc k) k≤n v1 v2 x .(intV 0) .k n-j≤n refl = intV 1 , 0 , refl , (I.+ 1 , refl)

  -- Relate λ x → 0 and λ x → x at any step count.
  example2 : ∀ n → relV (nat ⇒ nat) (closure (const (lit 0)) ∅) (closure (var this) ∅) n
  example2 n zero k≤n v1 v2 x = tt
  example2 n (suc k) k≤n (intV v1) (intV v2) x .(intV 0) .k n-j≤n refl = intV v2 , 0 , refl , (I.+ v2 , cong I.+_ (+-right-identity v2))

relρ : ∀ Γ (ρ1 ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
relρ ∅ ∅ ∅ n = ⊤
relρ (τ • Γ) (v1 • ρ1) (v2 • ρ2) n = relV τ v1 v2 n × relρ Γ ρ1 ρ2 n

relV-mono : ∀ m n → m ≤ n → ∀ τ v1 v2 → relV τ v1 v2 n → relV τ v1 v2 m
relV-mono m n m≤n nat (intV v1) (intV v2) vv = vv
relV-mono m n m≤n (σ ⇒ τ) (closure t1 ρ1) (closure t2 ρ2) ff k k≤m = ff k (≤-trans k≤m m≤n)

relρ-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 ρ2 → relρ Γ ρ1 ρ2 n → relρ Γ ρ1 ρ2 m
relρ-mono m n m≤n ∅ ∅ ∅ tt = tt
relρ-mono m n m≤n (τ • Γ) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = relV-mono m n m≤n _ v1 v2 vv , relρ-mono m n m≤n Γ ρ1 ρ2 ρρ

fundamentalV : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT (var x) (var x) ρ1 ρ2 n
fundamentalV x zero ρ1 ρ2 ρρ = tt
fundamentalV this (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) .v1 .n n-j≤n refl =  v2 , zero , refl , vv
fundamentalV (that x) (suc n) (v1 • ρ1) (v2 • ρ2) (vv , ρρ) = fundamentalV x (suc n) ρ1 ρ2 ρρ

lt1 : ∀ {k n} → k < n → k ≤ n
lt1 (s≤s p) = ≤-step p

-- relV-apply : ∀ {σ τ Γ} (s : Term Γ (σ ⇒ τ)) t v1 ρ2 n-j
--   n1 sv1 sv2
--   (svv : relV (σ ⇒ τ) sv1 sv2 n1)
--   n2 tv1 tv2
--   (tvv : relV σ tv1 tv2 (suc (suc n2)))
--   (eq : apply sv1 tv1 n2 ≡ Done v1 n-j) →
--   -- (tvv)
--   -- (eqv1)
--   Σ[ v2 ∈ Val τ ] Σ[ n2 ∈ ℕ ] Σ[ n3 ∈ ℕ ] eval (app s t) ρ2 n2 ≡ Done v2 n3 × relV τ v1 v2 (suc n-j)
-- relV-apply s t v1 ρ n-j n1 (closure st ρ1) (closure st2 ρ2) svv n2 tv1 tv2 tvv eq = {! !}
-- -- relV-apply s t v1 ρ2 n-j _ _ sv2 svv _ tv1 tv2 tvv eq

fundamental : ∀ {Γ τ} (t : Term Γ τ) → (n : ℕ) → (ρ1 ρ2 : ⟦ Γ ⟧Context) (ρρ : relρ Γ ρ1 ρ2 n) → relT t t ρ1 ρ2 n
fundamental t zero ρ1 ρ2 ρρ = tt
fundamental (var x) (suc n) ρ1 ρ2 ρρ = fundamentalV x (suc n) ρ1 ρ2 ρρ
fundamental (const (lit v)) (suc n) ρ1 ρ2 ρρ .(intV v) .n n-j≤n refl = intV v , zero , refl , I.+ zero , refl
fundamental (abs t) (suc n) ρ1 ρ2 ρρ .(closure t ρ1) .n n-j≤n refl =  closure t ρ2 , zero , refl , (λ k k≤n v1 v2 vv → fundamental t k (v1 • ρ1) (v2 • ρ2) (vv , relρ-mono k (suc n) (lt1 k≤n) _ _ _ ρρ))
fundamental (app s t) (suc zero) ρ1 ρ2 ρρ v1 n-j n-j≤n ()
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq with eval s ρ1 n | inspect (eval s ρ1) n
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq | Done sv1 n1 | [ s1eq ] with eval-dec s _ _ n n1 s1eq | eval t ρ1 n1 | inspect (eval t ρ1) n1
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n eq | Done (closure st1 sρ1) n1 | [ s1eq ] | n1≤n | Done tv1 n2 | [ t1eq ] with eval-dec t _ _ n1 n2 t1eq
... | n2≤n1 with fundamental s (suc (suc n)) ρ1 ρ2 ρρ (closure st1 sρ1) (suc n1) (s≤s n1≤n) (eval-mono s ρ1 (closure st1 sρ1) n n1 s1eq)
  | fundamental t (suc (suc n1)) ρ1 ρ2 (relρ-mono (suc (suc n1)) (suc (suc n)) (s≤s (s≤s n1≤n)) _ _ _ ρρ) tv1 (suc n2) (s≤s n2≤n1) (eval-mono t ρ1 tv1 n1 n2 t1eq)
... | sv2@(closure st2 sρ2) , sn3 , s2eq , svv | tv2 , tn3 , t2eq , tvv with svv (suc n2) (s≤s (s≤s n2≤n1)) tv1 tv2 (relV-mono _ _ (s≤s (n≤1+n n2)) _ _ _ tvv ) v1 n-j (eval-dec st1 _ _ _ _ eq) eq
... | v2 , n3 , eq2 , vv = v2 , suc (sn3 + (tn3 + n3)) , comp , vv
  where
    s2eq-adj : eval s ρ2 (sn3 + (tn3 + n3)) ≡ Done (closure st2 sρ2) (tn3 + n3)
    s2eq-adj rewrite +-comm sn3 (tn3 + n3)| cong (Done (closure st2 sρ2)) (sym (+-right-identity (tn3 + n3))) = eval-adjust-plus (tn3 + n3) s _ sv2 _ _ s2eq
    t2eq-adj : eval t ρ2 (tn3 + n3) ≡ Done tv2 n3
    t2eq-adj rewrite +-comm tn3 n3 | cong (Done tv2) (sym (+-right-identity n3)) = eval-adjust-plus n3 t _ tv2 _ _ t2eq

    comp : (eval s ρ2 >>= (λ sv → eval t ρ2 >>= apply sv))
      (sn3 + (tn3 + n3))
      ≡ Done v2 0
    comp rewrite s2eq-adj | t2eq-adj = eq2

fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Done sv1 n1 | [ s1eq ] | n1≤n | Error | [ t1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Done sv1 n1 | [ s1eq ] | n1≤n | TimeOut | [ t1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | Error | [ s1eq ]
fundamental (app s t) (suc (suc n)) ρ1 ρ2 ρρ v1 n-j n-j≤n () | TimeOut | [ s1eq ]
