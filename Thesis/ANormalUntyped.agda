{-# OPTIONS --allow-unsolved-metas #-}
module Thesis.ANormalUntyped where

open import Agda.Primitive
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Product
open import Data.Nat
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
data _⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : Term Γ → ℕ → Val Uni → Set

data _F⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) : Fun Γ → ℕ → Val Uni → Set where
  abs : ∀ {t : Fun (Uni • Γ)} →
    ρ F⊢ abs t ↓[ 0 ] closure t ρ
  term : ∀ {v} n (t : Term Γ) →
    ρ ⊢ t ↓[ n ] v →
    ρ F⊢ term t ↓[ n ] v

data _⊢_↓[_]_ {Γ} (ρ : ⟦ Γ ⟧Context) where
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

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : DTerm Γ → DVal DUni → Set

data _D_F⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : DFun Γ → DVal DUni → Set where
  dabs : ∀ {dt : DFun (Uni • Γ)} →
    ρ D dρ F⊢ dabs dt ↓ dclosure dt ρ dρ
  dterm : ∀ {dv} (dt : DTerm Γ) →
    ρ D dρ ⊢ dt ↓ dv →
    ρ D dρ F⊢ dterm dt ↓ dv

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) where
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

open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Binary hiding (_⇒_)

suc∸ : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
suc∸ m zero z≤n = refl
suc∸ (suc m) (suc n) (s≤s n≤m) = suc∸ m n n≤m

suc∸suc : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
suc∸suc (suc m) zero (s≤s n<m) = refl
suc∸suc (suc m) (suc n) (s≤s n<m) = suc∸suc m n n<m

lemlt : ∀ j k → suc j < k → k ∸ suc j < k
lemlt j (suc k) (s≤s j<k) = s≤s (∸-mono {k} {k} {j} {0} ≤-refl z≤n)

lemlt′ : ∀ j k → suc j <′ k → k ∸ suc j <′ k
lemlt′ j k j<′k = ≤⇒≤′ (lemlt j k (≤′⇒≤ j<′k))

open import Induction.WellFounded
open import Induction.Nat
rrelT3-Type : ℕ → Set₁
rrelT3-Type n =
  ∀ {Γ} → (t1 : Fun Γ) (dt : DFun Γ) (t2 : Fun Γ)
  (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → Set

rrelV3-Type : ℕ → Set₁
rrelV3-Type n = ∀ (v1 : Val Uni) (dv : DVal DUni) (v2 : Val Uni) → Set

rrelTV3-Type : ℕ → Set₁
rrelTV3-Type n = rrelT3-Type n × rrelV3-Type n

-- The type of the function availalbe for recursive calls.
rrelTV3-recSubCallsT : ℕ → Set₁
rrelTV3-recSubCallsT n = (k : ℕ) → k < n → rrelTV3-Type k

mutual
  -- Assemble together
  rrelTV3-step : ∀ n → rrelTV3-recSubCallsT n → rrelTV3-Type n
  rrelTV3-step n rec-rrelTV3 =
    let rrelV3-n = rrelV3-step n rec-rrelTV3
    in rrelT3-step n rec-rrelTV3 rrelV3-n , rrelV3-n
  rrelTV3 =  <-rec rrelTV3-Type rrelTV3-step
  rrelT3 : ∀ n → rrelT3-Type n
  rrelT3 n =  proj₁ (rrelTV3 n)
  rrelV3 : ∀ n → rrelV3-Type n
  rrelV3 n =  proj₂ (rrelTV3 n)

  s-rrelV3 :
    ∀ k → rrelTV3-recSubCallsT k → rrelV3-Type k →
    ∀ j → j < k → rrelV3-Type (k ∸ j)
  s-rrelV3 k rec-rrelTV3 rrelV3-k 0 _ = rrelV3-k
  s-rrelV3 k rec-rrelTV3 rrelV3-k (suc j) sucj<k = proj₂ (rec-rrelTV3 (k ∸ suc j) (lemlt j k sucj<k))
  -- Have the same context for t1, dt and t2? Yeah, good, that's what we want in the end...
  -- Though we might want more flexibility till when we have replacement
  -- changes.
  rrelT3-step : ∀ k → rrelTV3-recSubCallsT k →
    rrelV3-Type k →
    -- rrelV3-Type n
    ∀ {Γ} → (t1 : Fun Γ) (dt : DFun Γ) (t2 : Fun Γ)
      (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → Set
  rrelT3-step k rec-rrelTV3 rrelV3-k =
    λ t1 dt t2 ρ1 dρ ρ2 →
    ∀ j (j<k : j < k) n2 →
    (v1 v2 : Val Uni) →
    (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ j ] v1) →
    (ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) →
    Σ[ dv ∈ DVal DUni ] Σ[ dn ∈ ℕ ]
    ρ1 D dρ F⊢ dt ↓ dv ×
    s-rrelV3 k rec-rrelTV3 rrelV3-k j j<k v1 dv v2
    -- where
    --   s-rrelV3 : ∀ j → j <′ k → rrelV3-Type (k ∸ j)
    --   -- If j = 0, we can't do a recursive call on (k - j) because that's not
    --   -- well-founded. Luckily, we don't need to, just use relV as defined at
    --   -- the same level.
    --   -- Yet, this will be a pain in proofs.
    --   s-rrelV3 0 _ = rrelV3-k
    --   s-rrelV3 (suc j) sucj<′k = proj₂ (rec-rrelTV3 (k ∸ suc j) (lemlt′ j k sucj<′k))

  rrelV3-step : ∀ n → rrelTV3-recSubCallsT n →
    -- rrelV3-Type n
    ∀ (v1 : Val Uni) (dv : DVal DUni) (v2 : Val Uni) → Set
  rrelV3-step n rec-rrelTV3 (intV v1) (dintV dv) (intV v2) = dv I.+ (I.+ v1) ≡ (I.+ v2)
  rrelV3-step n rec-rrelTV3 (intV v1) (dintV n₁) (closure t ρ) = ⊥
  rrelV3-step n rec-rrelTV3 (intV v1) (dclosure dt ρ dρ) c = ⊥
  rrelV3-step n rec-rrelTV3 (closure {Γ1} t1 ρ1) (dclosure {ΔΓ} dt ρ' dρ) (closure {Γ2} t2 ρ2) =
      -- Require a proof that the two contexts match:
      Σ ((Γ1 ≡ Γ2) × (Γ1 ≡ ΔΓ)) λ { (refl , refl) →
        ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
        proj₂ (rec-rrelTV3 k k<n) v1 dv v2 →
        proj₁ (rec-rrelTV3 k k<n)
          t1
          dt
          t2
          (v1 • ρ1)
          (dv • dρ)
          (v2 • ρ2)
      }
  rrelV3-step n rec-rrelTV3 (closure t ρ) (dclosure dt ρ₁ dρ) (intV n₁) = ⊥
  rrelV3-step n rec-rrelTV3 (closure t ρ) (dintV n₁) c = ⊥

open import Postulate.Extensionality
mutual
  rrelT3-equiv : ∀ k {Γ} {t1 : Fun Γ} {dt t2 ρ1 dρ ρ2} →
    rrelT3 k t1 dt t2 ρ1 dρ ρ2 ≡
    ∀ j (j<k : j < k) n2 →
    ∀ (v1 v2 : Val Uni) →
    (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ j ] v1) →
    (ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) →
    Σ[ dv ∈ DVal DUni ] Σ[ dn ∈ ℕ ]
    ρ1 D dρ F⊢ dt ↓ dv ×
    rrelV3 j v1 dv v2
  rrelT3-equiv k {Γ} {t1} {dt} {t2} {ρ1} {dρ} {ρ2} =
    cong (λ □ → ∀ j → □ j) (ext
      λ {
        zero -> cong {lsuc lzero} {lsuc lzero} {{!!}} {{!!}} {!!} {{!!}} {{! !}} {!cong!}
        -- cong {{!!}} {{!!}}
        -- (λ (□ : zero < k → ∀ (n2 : ℕ) (v1 v2 : Val Uni) (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ zero ] v1)  → {!(ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) → ? !})→
        --              ∀ (j<k : zero < k) n2 →
        --              (v1 v2 : Val Uni) →
        --              (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ zero ] v1) →
        --              (ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) →
        --              Σ-syntax (DVal DUni)
        --              λ dv → Σ-syntax ℕ λ dn → (ρ1 D dρ F⊢ dt ↓ dv) × □ j<k n2 v1 v2 ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2)
        --           {!!}
        ;
        (suc j') -> {!!}})
    -- cong (λ □ →
    --      (j : ℕ) (j<k : j < k) (n2 : ℕ)
    --      (v1 v2 : Val Uni) →
    --      (ρ1⊢t1↓[j]v1 : ρ1 F⊢ t1 ↓[ j ] v1) →
    --      -- (ρ2⊢t2↓[n2]v2 : ρ2 F⊢ t2 ↓[ n2 ] v2) →
    --        □ j j<k n2 v1 v2 ρ1⊢t1↓[j]v1
    --     -- □ j<k n2 v1 v2 ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
    --     ) (ext³ λ j j<k n2 → {!ext³!})

  rrelV3-equiv : ∀ n {Γ1 Γ2 ΔΓ t1 dt t2 ρ1 ρ' dρ ρ2} →
    rrelV3 n (closure {Γ1} t1 ρ1) (dclosure {ΔΓ} dt ρ' dρ) (closure {Γ2} t2 ρ2) ≡ Σ ((Γ1 ≡ Γ2) × (Γ1 ≡ ΔΓ)) λ { (refl , refl) →
        ∀ (k : ℕ) (k<n : k <′ n) v1 dv v2 →
        rrelV3 k v1 dv v2 →
        rrelT3 k
          t1
          dt
          t2
          (v1 • ρ1)
          (dv • dρ)
          (v2 • ρ2)
      }
  rrelV3-equiv n = cong (λ □ → Σ (_ ≡ _ × _ ≡ _) □) (ext (λ { (eq1 , eq2) →
    cong
      (λ □ →
         (λ { (refl , refl)
                → ∀ (k : ℕ) (k<n : k <′ n) v1 dv v2 → □ k k<n v1 dv v2
            })
         eq1 eq2)
      (ext (λ x → ext {!!}))}))
  --
  -- cong (λ □ → ∀ k → (k<n : k <′ n) → □ k k<n)
  -- rrelV3-equiv k

rrelρ3 : ℕ → ∀ Γ (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → Set
rrelρ3 n ∅ ∅ ∅ ∅ = ⊤
rrelρ3 n (Uni • Γ) (v1 • ρ1) (dv • dρ) (v2 • ρ2) = rrelV3 n v1 dv v2 × rrelρ3 n Γ ρ1 dρ ρ2

--
rfundamental3 : ∀ {Γ} (t : Fun Γ) → ∀ k ρ1 dρ ρ2 → (ρρ : rrelρ3 k Γ ρ1 dρ ρ2) → rrelT3 k t (derive-dfun t) t ρ1 dρ ρ2
rfundamental3 (term x) k ρ1 dρ ρ2 ρρ j j<k n2 v1 v2 ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 = {!!}
rfundamental3 {Γ} (abs t) k ρ1 dρ ρ2 ρρ .0 j<k .0 (closure .t .ρ1) (closure .t .ρ2) abs abs = dclosure (derive-dfun t) ρ1 dρ , 0 , dabs , (refl , refl) , {!body !}
  where
    body1 : ∀ k₁ (k₁<k : k₁ <′ k) → (v1 : Val Uni) (dv : DVal DUni) (v2 : Val Uni) → rrelV3 k₁ v1 dv v2 → rrelT3 k₁ t (derive-dfun t) t (v1 • ρ1) (dv • dρ) (v2 • ρ2)
    body1 = λ k₁ k₁<k v1 dv v2 x v3 v4 j n2 j<k₁ ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 → {!
    rfundamental3 {Uni • Γ} t k₁ (v1 • ρ1) (dv • dρ) (v2 • ρ2) ({!vv!} , {!ρρ!}) v3 v4 0 n2 {!j<k₁ !} {! ρ1⊢t1↓[j]v1 !} ρ2⊢t2↓[n2]v2
    !}
  -- λ
  -- { k₁ k<n v1 dv v2 vv v3 v4 0 n2 j<k₁ ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 → {!
  -- rfundamental3 {Uni • Γ} t k₁ (v1 • ρ1) (dv • dρ) (v2 • ρ2) ({!vv!} , {!ρρ!}) v3 v4 0 n2 {!j<k₁ !} {! ρ1⊢t1↓[j]v1 !} ρ2⊢t2↓[n2]v2
  -- !}
  -- -- (Some.wfRec-builder rrelTV3-Type rrelTV3-step k₁
  --                     -- (<-well-founded′ k k₁ k<n))

  -- -- All.wfRec-builder <-well-founded _ rrelTV3-Type rrelTV3-step k k₁ k<n : rrelTV3-Type k₁
  -- --
  -- ; k₁ k<n v1 dv v2 vv v3 v4 (suc j) n2 j<k₁ ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 → {!
  -- !}
  -- -- rfundamental3 t k₁ (v1 • ρ1) (dv • dρ) (v2 • ρ2) ({!vv!} , {!ρρ!}) v3 v4 {!suc j !} n2 {!j<k₁ !} {! ρ1⊢t1↓[j]v1 !} ρ2⊢t2↓[n2]v2
  -- }

  --   -- ∀ k → rrelTV3-recSubCallsT k → rrelV3-Type k →
  --   -- ∀ j → j <′ k → rrelV3-Type (k ∸ j)
  --   foo : s-rrelV3 k
  --     (All.wfRec-builder <-well-founded _ rrelTV3-Type rrelTV3-step k)
  --     (rrelV3-step k (All.wfRec-builder <-well-founded _ rrelTV3-Type rrelTV3-step k))
  --     j j<k v1 (dclosure (derive-dfun t) ρ1 dρ) v2
  --   foo with j
  --   ... | s = {!!}
