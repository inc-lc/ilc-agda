module Thesis.ANormalUntyped where

open import Data.Nat.Base
open import Data.Integer.Base
open import Relation.Binary.PropositionalEquality

{- Typed deBruijn indexes for untyped languages. -}

-- Make this abstract again *and* add needed equations.
abstract
  data Type : Set where
    Uni : Type
  uni = Uni

  -- Allow exposing that there's a single type where needed.
  isUni : ∀ τ → τ ≡ uni
  isUni Uni = refl

-- This equation allows bypassing more checks. Otherwise we'd need to use isUni
-- even more often.
_⇒_ : Type → Type → Type
_⇒_ σ τ = τ

open import Base.Syntax.Context Type public
data Term (Γ : Context) (τ : Type) : Set where
  var : (x : Var Γ τ) →
    Term Γ τ
  lett : ∀ {σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → Term (τ₁ • Γ) τ → Term Γ τ

{-
deriveC Δ (lett f x t) = dlett df x dx
-}

-- data ΔCTerm (Γ : Context) (τ : Type) (Δ : Context) : Set where
-- data ΔCTerm (Γ : Context) (τ : Type) (Δ : Context) : Set where
--   cvar : (x : Var Γ τ) Δ →
--     ΔCTerm Γ τ Δ
--   clett : ∀ {σ τ₁ κ} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) →
--     ΔCTerm (τ₁ • Γ) τ (? • Δ) →
--     ΔCTerm Γ τ Δ

weaken-term : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term Γ₁ τ →
  Term Γ₂ τ
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (lett f x t) = lett (weaken-var Γ₁≼Γ₂ f) (weaken-var Γ₁≼Γ₂ x) (weaken-term (keep _ • Γ₁≼Γ₂) t)

data Fun (Γ : Context) : (τ : Type) → Set where
  term : ∀ {τ} → Term Γ τ → Fun Γ τ
  abs : ∀ {σ τ} → Fun (σ • Γ) τ → Fun Γ (σ ⇒ τ)

weaken-fun : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Fun Γ₁ τ →
  Fun Γ₂ τ
weaken-fun Γ₁≼Γ₂ (term x) = term (weaken-term Γ₁≼Γ₂ x)
weaken-fun Γ₁≼Γ₂ (abs f) = abs (weaken-fun (keep _ • Γ₁≼Γ₂) f)

data Val : Type → Set
-- data Val (τ : Type) : Set

open import Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

-- data Val (τ : Type) where
data Val where
  closure : ∀ {Γ σ τ} → (t : Fun (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  intV : ∀ {τ} (n : ℤ) → Val τ
-- ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
-- ⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
-- ⟦ lett f x t ⟧Term ρ = ⟦ t ⟧Term (⟦ f ⟧Var ρ (⟦ x ⟧Var ρ) • ρ)

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

eval-fun : ∀ {Γ τ} → Fun Γ τ → ⟦ Γ ⟧Context → Res τ
eval-term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply {σ} (closure {σ = σ₁} f ρ) a n with isUni σ | isUni σ₁
apply {.uni} (closure {_} {.uni} f ρ) a n | refl | refl = eval-fun f (a • ρ) n
apply (intV _) a n = Error

eval-term t ρ zero = TimeOut
eval-term (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
eval-term (lett f x t) ρ (suc n) = apply (⟦ f ⟧Var ρ) (⟦ x ⟧Var ρ) n >>= (λ v → eval-term t (v • ρ) n)

eval-fun (term t) ρ n = eval-term t ρ n
eval-fun (abs f) ρ n = Done (closure f ρ)

-- Erasure from typed to untyped values.
import Thesis.ANormalBigStep as T

erase-type : T.Type → Type
erase-type _ = uni

erase-val : ∀ {τ} → T.Val τ → Val (erase-type τ)

erase-errVal : ∀ {τ} → T.ErrVal τ → ErrVal (erase-type τ)
erase-errVal (T.Done v) = Done (erase-val v)
erase-errVal T.Error = Error
erase-errVal T.TimeOut = TimeOut

erase-res : ∀ {τ} → T.Res τ → Res (erase-type τ)
erase-res r n = erase-errVal (r n)

erase-ctx : T.Context → Context
erase-ctx ∅ = ∅
erase-ctx (τ • Γ) = erase-type τ • (erase-ctx Γ)

erase-env : ∀ {Γ} → T.Op.⟦ Γ ⟧Context → ⟦ erase-ctx Γ ⟧Context
erase-env ∅ = ∅
erase-env (v • ρ) = erase-val v • erase-env ρ

erase-var : ∀ {Γ τ} → T.Var Γ τ → Var (erase-ctx Γ) (erase-type τ)
erase-var T.this = this
erase-var (T.that x) = that (erase-var x)

erase-term : ∀ {Γ τ} → T.Term Γ τ → Term (erase-ctx Γ) (erase-type τ)
erase-term (T.var x) = var (erase-var x)
erase-term (T.lett f x t) = lett (erase-var f) (erase-var x) (erase-term t)

erase-fun : ∀ {Γ τ} → T.Fun Γ τ → Fun (erase-ctx Γ) (erase-type τ)
erase-fun (T.term x) = term (erase-term x)
erase-fun (T.abs f) = abs (erase-fun f)

erase-val (T.closure t ρ) = closure (erase-fun t) (erase-env ρ)
erase-val (T.intV n) = intV n

-- Different erasures commute.
erasure-commute-var : ∀ {Γ τ} (x : T.Var Γ τ) ρ →
  erase-val (T.Op.⟦ x ⟧Var ρ) ≡ ⟦ erase-var x ⟧Var (erase-env ρ)
erasure-commute-var T.this (v • ρ) = refl
erasure-commute-var (T.that x) (v • ρ) = erasure-commute-var x ρ

erase-bind : ∀ {σ τ Γ} a (t : T.Term (σ • Γ) τ) ρ n → erase-errVal (a T.>>= (λ v → T.eval-term t (v • ρ) n)) ≡ erase-errVal a >>= (λ v → eval-term (erase-term t) (v • erase-env ρ) n)

erasure-commute-fun : ∀ {Γ τ} (t : T.Fun Γ τ) ρ n →
  erase-errVal (T.eval-fun t ρ n) ≡ eval-fun (erase-fun t) (erase-env ρ) n

erasure-commute-apply : ∀ {σ τ} (f : T.Val (σ T.⇒ τ)) a n → erase-errVal (T.apply f a n) ≡ apply (erase-val f) (erase-val a) n
erasure-commute-apply {σ} (T.closure t ρ) a n with isUni (erase-type σ)
erasure-commute-apply {σ} (T.closure t ρ) a n | refl = erasure-commute-fun t (a • ρ) n

erasure-commute-term : ∀ {Γ τ} (t : T.Term Γ τ) ρ n →
  erase-errVal (T.eval-term t ρ n) ≡ eval-term (erase-term t) (erase-env ρ) n

erasure-commute-fun (T.term t) ρ n = erasure-commute-term t ρ n
erasure-commute-fun (T.abs t) ρ n = refl

erasure-commute-term t ρ zero = refl
erasure-commute-term (T.var x) ρ (ℕ.suc n) = cong Done (erasure-commute-var x ρ)
erasure-commute-term (T.lett f x t) ρ (ℕ.suc n) rewrite erase-bind (T.apply (T.Op.⟦ f ⟧Var ρ) (T.Op.⟦ x ⟧Var ρ) n) t ρ n | erasure-commute-apply (T.Op.⟦ f ⟧Var ρ) (T.Op.⟦ x ⟧Var ρ) n | erasure-commute-var f ρ | erasure-commute-var x ρ = refl

erase-bind (T.Done v) t ρ n = erasure-commute-term t (v • ρ) n
erase-bind T.Error t ρ n = refl
erase-bind T.TimeOut t ρ n = refl
