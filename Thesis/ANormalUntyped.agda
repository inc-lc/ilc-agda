module Thesis.ANormalUntyped where

open import Data.Nat.Base
open import Data.Integer.Base
open import Relation.Binary.PropositionalEquality

{- Typed deBruijn indexes for untyped languages. -}

-- Using a record gives an eta rule saying that all types are equal.
record Type : Set where
  constructor Uni

open import Base.Syntax.Context Type public
data Term (Γ : Context) : Set where
  var : (x : Var Γ Uni) →
    Term Γ
  lett : (f : Var Γ Uni) → (x : Var Γ Uni) → Term (Uni • Γ) → Term Γ

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

weaken-term : ∀ {Γ₁ Γ₂} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term Γ₁ →
  Term Γ₂
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (lett f x t) = lett (weaken-var Γ₁≼Γ₂ f) (weaken-var Γ₁≼Γ₂ x) (weaken-term (keep _ • Γ₁≼Γ₂) t)

data Fun (Γ : Context) : Set where
  term : Term Γ → Fun Γ
  abs : ∀ {σ} → Fun (σ • Γ) → Fun Γ

weaken-fun : ∀ {Γ₁ Γ₂} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Fun Γ₁ →
  Fun Γ₂
weaken-fun Γ₁≼Γ₂ (term x) = term (weaken-term Γ₁≼Γ₂ x)
weaken-fun Γ₁≼Γ₂ (abs f) = abs (weaken-fun (keep _ • Γ₁≼Γ₂) f)

data Val : Type → Set
-- data Val (τ : Type) : Set

open import Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

-- data Val (τ : Type) where
data Val where
  closure : ∀ {Γ} → (t : Fun (Uni • Γ)) → (ρ : ⟦ Γ ⟧Context) → Val Uni
  intV : ∀ (n : ℤ) → Val Uni
-- ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
-- ⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
-- ⟦ lett f x t ⟧Term ρ = ⟦ t ⟧Term (⟦ f ⟧Var ρ (⟦ x ⟧Var ρ) • ρ)

data ErrVal : Set where
  Done : (v : Val Uni) → ErrVal
  Error : ErrVal
  TimeOut : ErrVal

_>>=_ : ErrVal → (Val Uni → ErrVal) → ErrVal
Done v >>= f = f v
Error >>= f = Error
TimeOut >>= f = TimeOut

Res : Set
Res = ℕ → ErrVal

eval-fun : ∀ {Γ} → Fun Γ → ⟦ Γ ⟧Context → Res
eval-term : ∀ {Γ} → Term Γ → ⟦ Γ ⟧Context → Res

apply : Val Uni → Val Uni → Res
apply (closure f ρ) a n = eval-fun f (a • ρ) n
apply (intV _) a n = Error

eval-term t ρ zero = TimeOut
eval-term (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
eval-term (lett f x t) ρ (suc n) = apply (⟦ f ⟧Var ρ) (⟦ x ⟧Var ρ) n >>= (λ v → eval-term t (v • ρ) n)

eval-fun (term t) ρ n = eval-term t ρ n
eval-fun (abs f) ρ n = Done (closure f ρ)

-- Erasure from typed to untyped values.
import Thesis.ANormalBigStep as T

erase-type : T.Type → Type
erase-type _ = Uni

erase-val : ∀ {τ} → T.Val τ → Val (erase-type τ)

erase-errVal : ∀ {τ} → T.ErrVal τ → ErrVal
erase-errVal (T.Done v) = Done (erase-val v)
erase-errVal T.Error = Error
erase-errVal T.TimeOut = TimeOut

erase-res : ∀ {τ} → T.Res τ → Res
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

erase-term : ∀ {Γ τ} → T.Term Γ τ → Term (erase-ctx Γ)
erase-term (T.var x) = var (erase-var x)
erase-term (T.lett f x t) = lett (erase-var f) (erase-var x) (erase-term t)

erase-fun : ∀ {Γ τ} → T.Fun Γ τ → Fun (erase-ctx Γ)
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
erasure-commute-apply {σ} (T.closure t ρ) a n = erasure-commute-fun t (a • ρ) n

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
