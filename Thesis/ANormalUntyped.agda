module Thesis.ANormalUntyped where

open import Data.Empty
open import Data.Product
open import Data.Nat.Base
import Data.Integer.Base as I
open I using (ℤ)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality

{- Typed deBruijn indexes for untyped languages. -}

-- Using a record gives an eta rule saying that all types are equal.
record Type : Set where
  constructor Uni

record DType : Set where
  constructor DUni

open import Base.Syntax.Context Type public
import Base.Syntax.Context DType as DC

data Term (Γ : Context) : Set where
  var : (x : Var Γ Uni) →
    Term Γ
  lett : (f : Var Γ Uni) → (x : Var Γ Uni) → Term (Uni • Γ) → Term Γ

ΔΔ : Context → DC.Context
ΔΔ ∅ = ∅
ΔΔ (τ • Γ) = DUni • ΔΔ Γ

derive-dvar : ∀ {Δ} → (x : Var Δ Uni) → DC.Var (ΔΔ Δ) DUni
derive-dvar this = DC.this
derive-dvar (that x) = DC.that (derive-dvar x)

data DTerm : (Δ : Context) → Set where
  dvar : ∀ {Δ} (x : DC.Var (ΔΔ Δ) DUni) →
    DTerm Δ
  dlett : ∀ {Δ} →
    (f : Var Δ Uni) →
    (x : Var Δ Uni) →
    (t : Term (Uni • Δ)) →
    (df : DC.Var (ΔΔ Δ) DUni) →
    (dx : DC.Var (ΔΔ Δ) DUni) →
    (dt : DTerm (Uni • Δ)) →
    DTerm Δ

derive-dterm : ∀ {Δ} → (t : Term Δ) → DTerm Δ
derive-dterm (var x) = dvar (derive-dvar x)
derive-dterm (lett f x t) =
  dlett f x t (derive-dvar f) (derive-dvar x) (derive-dterm t)

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

-- I don't necessarily recommend having a separate syntactic category for
-- functions, but we should prove a fundamental lemma for them too, somehow.
-- I'll probably end up with some ANF allowing lambdas to do the semantics.
data Fun (Γ : Context) : Set where
  term : Term Γ → Fun Γ
  abs : ∀ {σ} → Fun (σ • Γ) → Fun Γ

data DFun (Δ : Context) : Set where
  dterm : DTerm Δ → DFun Δ
  dabs : DFun (Uni • Δ) → DFun Δ

derive-dfun : ∀ {Δ} → (t : Fun Δ) → DFun Δ
derive-dfun (term t) = dterm (derive-dterm t)
derive-dfun (abs f) = dabs (derive-dfun f)

weaken-fun : ∀ {Γ₁ Γ₂} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Fun Γ₁ →
  Fun Γ₂
weaken-fun Γ₁≼Γ₂ (term x) = term (weaken-term Γ₁≼Γ₂ x)
weaken-fun Γ₁≼Γ₂ (abs f) = abs (weaken-fun (keep _ • Γ₁≼Γ₂) f)

data Val : Type → Set
data DVal : DType → Set
-- data Val (τ : Type) : Set

open import Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

import Base.Denotation.Environment DType DVal as D

-- data Val (τ : Type) where
data Val where
  closure : ∀ {Γ} → (t : Fun (Uni • Γ)) → (ρ : ⟦ Γ ⟧Context) → Val Uni
  intV : ∀ (n : ℕ) → Val Uni

data DVal where
  dclosure : ∀ {Γ} → (dt : DFun (Uni • Γ)) → (ρ : ⟦ Γ ⟧Context) → (dρ : D.⟦ ΔΔ Γ ⟧Context) → DVal DUni
  dintV : ∀ (n : ℤ) → DVal DUni

ChΔ : ∀ (Δ : Context) → Set
ChΔ Δ = D.⟦ ΔΔ Δ ⟧Context

-- ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
-- ⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
-- ⟦ lett f x t ⟧Term ρ = ⟦ t ⟧Term (⟦ f ⟧Var ρ (⟦ x ⟧Var ρ) • ρ)

-- XXX separate syntax is a bit dangerous. Also, do I want to be so accurate relative to the original model?
data _F⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : Fun Γ → ℕ → Val Uni → Set where
  abs : ∀ {t : Fun (Uni • Γ)} →
    ρ F⊢ abs t ↓[ 0 ] closure t ρ

data _⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : Term Γ → ℕ → Val Uni → Set where
  var : ∀ (x : Var Γ Uni) →
    ρ ⊢ var x ↓[ 0 ] (⟦ x ⟧Var ρ)
  lett : ∀ n1 n2 {Γ' ρ′ v1 v2 v3} {f x t t'}  →
    ρ ⊢ var f ↓[ 0 ] closure {Γ'} t' ρ′ →
    ρ ⊢ var x ↓[ 0 ] v1 →
    (v1 • ρ′) F⊢ t' ↓[ n1 ] v2 →
    (v2 • ρ) ⊢ t ↓[ n2 ] v3 →
    ρ ⊢ lett f x t ↓[ suc (suc (n1 + n2)) ] v3
  -- lit : ∀ n →
  --   ρ ⊢ const (lit n) ↓[ 0 ] intV n

-- data _D_⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : D.⟦ ΔΔ Γ ⟧Context) : DTerm Γ → ℕ → DVal DUni → Set where
--   dvar : ∀ (x : DC.Var (ΔΔ Γ) DUni) →
--     ρ D dρ ⊢ dvar x ↓[ 0 ] (D.⟦ x ⟧Var dρ)
--   dlett : ∀ n1 n2 n3 n4 {Γ' ρ′ ρ'' dρ' v1 v2 v3 dv1 dv2 dv3} {f x t df dx dt t' dt'}  →
--     ρ ⊢ var f ↓[ 0 ] closure {Γ'} t' ρ′ →
--     ρ ⊢ var x ↓[ 0 ] v1 →
--     (v1 • ρ′) F⊢ t' ↓[ n1 ] v2 →
--     (v2 • ρ) ⊢ t ↓[ n2 ] v3 →
--     -- With a valid input ρ' and ρ'' coincide? Varies among plausible validity
--     -- definitions.
--     ρ D dρ ⊢ dvar df ↓[ 0 ] dclosure {Γ'} dt' ρ'' dρ' →
--     ρ D dρ ⊢ dvar dx ↓[ 0 ] dv1 →
--     (v1 • ρ'') D (dv1 • dρ') F⊢ dt' ↓[ n3 ] dv2 →
--     (v2 • ρ) D (dv2 • dρ) ⊢ dt ↓[ n4 ] dv3 →
--     ρ D dρ ⊢ dlett f x t df dx dt ↓[ suc (suc (n1 + n2)) ] dv3


-- Do I need to damn count steps here? No.

data _D_F⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : DFun Γ → DVal DUni → Set where
  dabs : ∀ {t : DFun (Uni • Γ)} →
    ρ D dρ F⊢ dabs t ↓ dclosure t ρ dρ

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : DTerm Γ → DVal DUni → Set where
  dvar : ∀ (x : DC.Var (ΔΔ Γ) DUni) →
    ρ D dρ ⊢ dvar x ↓ (D.⟦ x ⟧Var dρ)
  dlett : ∀ n1 n2 {Γ' ρ′ ρ'' dρ' v1 v2 v3 dv1 dv2 dv3} {f x t df dx dt t' dt'}  →
    ρ ⊢ var f ↓[ 0 ] closure {Γ'} t' ρ′ →
    ρ ⊢ var x ↓[ 0 ] v1 →
    (v1 • ρ′) F⊢ t' ↓[ n1 ] v2 →
    (v2 • ρ) ⊢ t ↓[ n2 ] v3 →
    -- With a valid input ρ' and ρ'' coincide? Varies among plausible validity
    -- definitions.
    ρ D dρ ⊢ dvar df ↓ dclosure {Γ'} dt' ρ'' dρ' →
    ρ D dρ ⊢ dvar dx ↓ dv1 →
    (v1 • ρ'') D (dv1 • dρ') F⊢ dt' ↓ dv2 →
    (v2 • ρ) D (dv2 • dρ) ⊢ dt ↓ dv3 →
    ρ D dρ ⊢ dlett f x t df dx dt ↓ dv3

{-# TERMINATING #-} -- Dear lord. Why on Earth.
mutual
  -- Single context? Yeah, good, that's what we want in the end...
  -- Though we might want more flexibility till when we have replacement
  -- changes.
  rrelT3 : ∀ {Γ} (t1 : Fun Γ) (dt : DFun Γ) (t2 : Fun Γ) (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  rrelT3 t1 dt t2 ρ1 dρ ρ2 k =
    (v1 v2 : Val Uni) →
    ∀ j n2 (j<k : j < k) →
    (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ j ] v1) →
    (ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) →
    Σ[ dv ∈ DVal DUni ] Σ[ dn ∈ ℕ ]
    ρ1 D dρ F⊢ dt ↓ dv ×
    rrelV3 v1 dv v2 (k ∸ j)

  rrelV3 : ∀ (v1 : Val Uni) (dv : DVal DUni) (v2 : Val Uni) → ℕ → Set
  rrelV3 (intV v1) (dintV dv) (intV v2) n = dv I.+ (I.+ v1) ≡ (I.+ v2)
  rrelV3 (closure {Γ1} t1 ρ1) (dclosure {ΔΓ} dt ρ' dρ) (closure {Γ2} t2 ρ2) n =
      -- Require a proof that the two contexts match:
      Σ ((Γ1 ≡ Γ2) × (Γ1 ≡ ΔΓ)) λ { (refl , refl) →
        ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
        rrelV3 v1 dv v2 k →
        rrelT3
          t1
          dt
          t2
          (v1 • ρ1)
          (dv • dρ)
          (v2 • ρ2)
          k
      }
  rrelV3 _ _ _ n = ⊥

-- -- [_]τ  from v1 to v2) :
-- -- [ τ ]τ dv from v1 to v2) =

-- -- data [_]Δ_from_to_ : ∀ Δ → ChΔ Δ → (ρ1 ρ2 : ⟦ Δ ⟧Context) → Set where
-- --   v∅ : [ ∅ ]Δ ∅ from ∅ to ∅
-- --   _v•_ : ∀ {τ Δ dv v1 v2 dρ ρ1 ρ2} →
-- --     (dvv : [ τ ]τ dv from v1 to v2) →
-- --     (dρρ : [ Δ ]Δ dρ from ρ1 to ρ2) →
-- --     [ τ • Δ ]Δ (dv • dρ) from (v1 • ρ1) to (v2 • ρ2)

-- data ErrVal : Set where
--   Done : (v : Val Uni) → ErrVal
--   Error : ErrVal
--   TimeOut : ErrVal

-- _>>=_ : ErrVal → (Val Uni → ErrVal) → ErrVal
-- Done v >>= f = f v
-- Error >>= f = Error
-- TimeOut >>= f = TimeOut

-- Res : Set
-- Res = ℕ → ErrVal

-- -- eval-fun : ∀ {Γ} → Fun Γ → ⟦ Γ ⟧Context → Res
-- -- eval-term : ∀ {Γ} → Term Γ → ⟦ Γ ⟧Context → Res

-- -- apply : Val Uni → Val Uni → Res
-- -- apply (closure f ρ) a n = eval-fun f (a • ρ) n
-- -- apply (intV _) a n = Error

-- -- eval-term t ρ zero = TimeOut
-- -- eval-term (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
-- -- eval-term (lett f x t) ρ (suc n) = apply (⟦ f ⟧Var ρ) (⟦ x ⟧Var ρ) n >>= (λ v → eval-term t (v • ρ) n)

-- -- eval-fun (term t) ρ n = eval-term t ρ n
-- -- eval-fun (abs f) ρ n = Done (closure f ρ)

-- -- -- Erasure from typed to untyped values.
-- -- import Thesis.ANormalBigStep as T

-- -- erase-type : T.Type → Type
-- -- erase-type _ = Uni

-- -- erase-val : ∀ {τ} → T.Val τ → Val (erase-type τ)

-- -- erase-errVal : ∀ {τ} → T.ErrVal τ → ErrVal
-- -- erase-errVal (T.Done v) = Done (erase-val v)
-- -- erase-errVal T.Error = Error
-- -- erase-errVal T.TimeOut = TimeOut

-- -- erase-res : ∀ {τ} → T.Res τ → Res
-- -- erase-res r n = erase-errVal (r n)

-- -- erase-ctx : T.Context → Context
-- -- erase-ctx ∅ = ∅
-- -- erase-ctx (τ • Γ) = erase-type τ • (erase-ctx Γ)

-- -- erase-env : ∀ {Γ} → T.Op.⟦ Γ ⟧Context → ⟦ erase-ctx Γ ⟧Context
-- -- erase-env ∅ = ∅
-- -- erase-env (v • ρ) = erase-val v • erase-env ρ

-- -- erase-var : ∀ {Γ τ} → T.Var Γ τ → Var (erase-ctx Γ) (erase-type τ)
-- -- erase-var T.this = this
-- -- erase-var (T.that x) = that (erase-var x)

-- -- erase-term : ∀ {Γ τ} → T.Term Γ τ → Term (erase-ctx Γ)
-- -- erase-term (T.var x) = var (erase-var x)
-- -- erase-term (T.lett f x t) = lett (erase-var f) (erase-var x) (erase-term t)

-- -- erase-fun : ∀ {Γ τ} → T.Fun Γ τ → Fun (erase-ctx Γ)
-- -- erase-fun (T.term x) = term (erase-term x)
-- -- erase-fun (T.abs f) = abs (erase-fun f)

-- -- erase-val (T.closure t ρ) = closure (erase-fun t) (erase-env ρ)
-- -- erase-val (T.intV n) = intV n

-- -- -- Different erasures commute.
-- -- erasure-commute-var : ∀ {Γ τ} (x : T.Var Γ τ) ρ →
-- --   erase-val (T.Op.⟦ x ⟧Var ρ) ≡ ⟦ erase-var x ⟧Var (erase-env ρ)
-- -- erasure-commute-var T.this (v • ρ) = refl
-- -- erasure-commute-var (T.that x) (v • ρ) = erasure-commute-var x ρ

-- -- erase-bind : ∀ {σ τ Γ} a (t : T.Term (σ • Γ) τ) ρ n → erase-errVal (a T.>>= (λ v → T.eval-term t (v • ρ) n)) ≡ erase-errVal a >>= (λ v → eval-term (erase-term t) (v • erase-env ρ) n)

-- -- erasure-commute-fun : ∀ {Γ τ} (t : T.Fun Γ τ) ρ n →
-- --   erase-errVal (T.eval-fun t ρ n) ≡ eval-fun (erase-fun t) (erase-env ρ) n

-- -- erasure-commute-apply : ∀ {σ τ} (f : T.Val (σ T.⇒ τ)) a n → erase-errVal (T.apply f a n) ≡ apply (erase-val f) (erase-val a) n
-- -- erasure-commute-apply {σ} (T.closure t ρ) a n = erasure-commute-fun t (a • ρ) n

-- -- erasure-commute-term : ∀ {Γ τ} (t : T.Term Γ τ) ρ n →
-- --   erase-errVal (T.eval-term t ρ n) ≡ eval-term (erase-term t) (erase-env ρ) n

-- -- erasure-commute-fun (T.term t) ρ n = erasure-commute-term t ρ n
-- -- erasure-commute-fun (T.abs t) ρ n = refl

-- -- erasure-commute-term t ρ zero = refl
-- -- erasure-commute-term (T.var x) ρ (ℕ.suc n) = cong Done (erasure-commute-var x ρ)
-- -- erasure-commute-term (T.lett f x t) ρ (ℕ.suc n) rewrite erase-bind (T.apply (T.Op.⟦ f ⟧Var ρ) (T.Op.⟦ x ⟧Var ρ) n) t ρ n | erasure-commute-apply (T.Op.⟦ f ⟧Var ρ) (T.Op.⟦ x ⟧Var ρ) n | erasure-commute-var f ρ | erasure-commute-var x ρ = refl

-- -- erase-bind (T.Done v) t ρ n = erasure-commute-term t (v • ρ) n
-- -- erase-bind T.Error t ρ n = refl
-- -- erase-bind T.TimeOut t ρ n = refl
