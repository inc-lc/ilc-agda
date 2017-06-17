-- Step-indexed logical relations based on relational big-step semantics
-- for ILC-based incremental computation.

-- Goal: prove the fundamental lemma for a ternary logical relation (change
-- validity) across t1, dt and t2. The fundamnetal lemma relates t, derive t and
-- t. That is, we relate a term evaluated relative to an original environment,
-- its derivative evaluated relative to a valid environment change, and the
-- original term evaluated relative to an updated environment.
--
-- Missing goal: here ⊕ isn't defined and wouldn't yet agree with change
-- validity.
--
-- This development is strongly inspired by "Imperative self-adjusting
-- computation" (ISAC below), POPL'08, including the choice of using ANF syntax
-- to simplify some step-indexing proofs.
--
-- In fact, this development is typed, hence some parts of the model are closer
-- to Ahmed (ESOP 2006), "Step-Indexed Syntactic Logical Relations for Recursive
-- and Quantified Types". But for many relevant aspects, the two papers are
-- very similar. In fact, I first defined similar logical relations
-- without types, but they require a trickier recursion scheme for well-founded
-- recursion, and I failed to do any proof in that setting.
--
-- The original inspiration came from Dargaye and Leroy (2010), "A verified
-- framework for higher-order uncurrying optimizations", but we ended up looking
-- at their source.
--
-- The main insight from the ISAC paper missing from the other one is how to
-- step-index a big-step semantics correctly: just ensure that the steps in the
-- big-step semantics agree with the ones in the small-step semantics. *Then*
-- everything just works with big-step semantics. Quite a few other details are
-- fiddly, but those are the same in small-step semantics.
--
-- The crucial novelty here is that we relate two computations on different
-- inputs. So we only conclude their results are related if both terminate; the
-- relation for computations does not prove that if the first computation
-- terminates, then the second terminates as well.
--
-- Instead, e1, de and e2 are related at k steps if, whenever e1 terminates in j
-- < k steps and e2 terminates with any step count, then de terminates (with any
-- step count) and their results are related at k - j steps.
--
-- Even when e1 terminates in j steps implies that e2 terminates, e2 gets no
-- bound. Similarly, we do not bound in how many steps de terminates, since on
-- big inputs it might take long.

module Thesis.StepIndexedRelBigStepTypedAnfIlcCorrect where

open import Data.Empty
open import Data.Unit.Base hiding (_≤_)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat -- using (ℕ; zero; suc; decTotalOrder; _<_; _≤_)
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open DecTotalOrder Data.Nat.decTotalOrder using () renaming (refl to ≤-refl; trans to ≤-trans)

data Type : Set where
  _⇒_ : (σ τ : Type) → Type
  nat : Type
infixr 20 _⇒_

open import Base.Syntax.Context Type public
open import Base.Syntax.Vars Type public

-- Decidable equivalence for types and contexts. Needed later for ⊕ on closures.

⇒-inj : ∀ {τ1 τ2 τ3 τ4 : Type} → _≡_ {A = Type} (τ1 ⇒ τ2) (τ3 ⇒ τ4) → τ1 ≡ τ3 × τ2 ≡ τ4
⇒-inj refl = refl , refl

_≟Type_ : (τ1 τ2 : Type) → Dec (τ1 ≡ τ2)
(τ1 ⇒ τ2) ≟Type (τ3 ⇒ τ4) with τ1 ≟Type τ3 | τ2 ≟Type τ4
(τ1 ⇒ τ2) ≟Type (.τ1 ⇒ .τ2) | yes refl | yes refl = yes refl
(τ1 ⇒ τ2) ≟Type (.τ1 ⇒ τ4) | yes refl | no ¬q = no (λ x → ¬q (proj₂ (⇒-inj x)))
(τ1 ⇒ τ2) ≟Type (τ3 ⇒ τ4) | no ¬p | q = no (λ x → ¬p (proj₁ (⇒-inj x)))
(τ1 ⇒ τ2) ≟Type nat = no (λ ())
nat ≟Type (τ2 ⇒ τ3) = no (λ ())
nat ≟Type nat = yes refl

•-inj : ∀ {τ1 τ2 : Type} {Γ1 Γ2 : Context} → _≡_ {A = Context} (τ1 • Γ1) (τ2 • Γ2) → τ1 ≡ τ2 × Γ1 ≡ Γ2
•-inj refl = refl , refl

_≟Ctx_ : (Γ1 Γ2 : Context) → Dec (Γ1 ≡ Γ2)
∅ ≟Ctx ∅ = yes refl
∅ ≟Ctx (τ2 • Γ2) = no (λ ())
(τ1 • Γ1) ≟Ctx ∅ = no (λ ())
(τ1 • Γ1) ≟Ctx (τ2 • Γ2) with τ1 ≟Type τ2 | Γ1 ≟Ctx Γ2
(τ1 • Γ1) ≟Ctx (.τ1 • .Γ1) | yes refl | yes refl = yes refl
(τ1 • Γ1) ≟Ctx (.τ1 • Γ2) | yes refl | no ¬q = no (λ x → ¬q (proj₂ (•-inj x)))
(τ1 • Γ1) ≟Ctx (τ2 • Γ2) | no ¬p | q = no (λ x → ¬p (proj₁ (•-inj x)))

≟Ctx-refl : ∀ Γ → Γ ≟Ctx Γ ≡ yes refl
≟Ctx-refl Γ with Γ ≟Ctx Γ
≟Ctx-refl Γ | yes refl = refl
≟Ctx-refl Γ | no ¬p = ⊥-elim (¬p refl)

data Const : (τ : Type) → Set where
  lit : ℕ → Const nat
  -- Adding this changes nothing without changes to the semantics.
  succ : Const (nat ⇒ nat)

data Term (Γ : Context) (τ : Type) : Set
-- Source values
data SVal (Γ : Context) : (τ : Type) → Set where
  var : ∀ {τ} →
    (x : Var Γ τ) →
    SVal Γ τ
  abs : ∀ {σ τ}
    (t : Term (σ • Γ) τ) →
    SVal Γ (σ ⇒ τ)
data Term (Γ : Context) (τ : Type) where
  val :
    SVal Γ τ →
    Term Γ τ
  -- constants aka. primitives
  const :
    (c : Const τ) →
    Term Γ τ
  -- we use de Bruijn indices, so we don't need binding occurrences.
  app : ∀ {σ}
    (vs : SVal Γ (σ ⇒ τ)) →
    (vt : SVal Γ σ) →
    Term Γ τ
  lett : ∀ {σ}
    (s : Term Γ σ) →
    (t : Term (σ • Γ) τ) →
    Term Γ τ

⟦_⟧Type : Type → Set
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
⟦ nat ⟧Type = ℕ

data Val : Type → Set

import Base.Denotation.Environment
module Den = Base.Denotation.Environment Type ⟦_⟧Type
open Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

⟦_⟧Const : ∀ {τ} → Const τ → ⟦ τ ⟧Type
⟦ lit n ⟧Const = n
⟦ succ ⟧Const = suc

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦_⟧SVal : ∀ {Γ τ} → SVal Γ τ → Den.⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ var x ⟧SVal ρ = Den.⟦ x ⟧Var ρ
⟦ abs t ⟧SVal ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ const c ⟧Term ρ = ⟦ c ⟧Const
⟦ val sv ⟧Term ρ = ⟦ sv ⟧SVal ρ
⟦ app s t ⟧Term ρ = ⟦ s ⟧SVal ρ (⟦ t ⟧SVal ρ)
⟦ lett s t ⟧Term ρ = ⟦ t ⟧Term ((⟦ s ⟧Term ρ) • ρ)

data Val where
  closure : ∀ {Γ σ τ} → (t : Term (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  natV : ∀ (n : ℕ) → Val nat

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → ⟦ Γ ⟧Context → Den.⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Term) (v • ⟦ ρ ⟧Env)
⟦ natV n ⟧Val = n

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  Den.⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ ⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

import Data.Integer as I
open I using (ℤ)

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

-- Check it's fine to use i 1 in the above proofs.
↓-sv-1-step : ∀ {Γ τ ρ v} {n} {sv : SVal Γ τ} →
  ρ ⊢ val sv ↓[ i' n ] v →
  n ≡ 1
↓-sv-1-step abs = refl
↓-sv-1-step (var x) = refl

↓-sound : ∀ {Γ τ ρ v hasIdx} {n : Idx hasIdx} {t : Term Γ τ} →
  ρ ⊢ t ↓[ n ] v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val
↓-sound abs = refl
↓-sound (app _ _ ↓₁ ↓₂ ↓′) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ | ↓-sound ↓′ = refl
↓-sound (var x) = ↦-sound _ x
↓-sound (lit n) = refl
↓-sound (lett n1 n2 vsv s t ↓ ↓₁) rewrite ↓-sound ↓ | ↓-sound ↓₁ = refl
-- ↓-sound (add ↓₁ ↓₂) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ = refl
-- ↓-sound (minus ↓₁ ↓₂) rewrite ↓-sound ↓₁ | ↓-sound ↓₂ = refl

-- No proof of completeness yet: the statement does not hold here.

-- data DType : Set where
--   _⇒_ : (σ τ : DType) → DType
--   int : DType
DType = Type

import Base.Syntax.Context DType as DC

Δτ : Type → DType
Δτ (σ ⇒ τ) = σ ⇒ Δτ σ ⇒ Δτ τ
Δτ nat = nat

ΔΔ : Context → DC.Context
ΔΔ ∅ = ∅
ΔΔ (τ • Γ) = Δτ τ • ΔΔ Γ
--ΔΔ Γ = Γ

-- A DTerm evaluates in normal context Δ, change context (ΔΔ Δ), and produces
-- a result of type (Δt τ).
data DTerm (Δ : Context) (τ : DType) : Set
data DSVal (Δ : Context) : (τ : DType) → Set where
  dvar : ∀ {τ} →
    (x : Var (ΔΔ Δ) (Δτ τ)) →
    DSVal Δ τ
  dabs : ∀ {σ τ}
    (dt : DTerm (σ • Δ) τ) →
    DSVal Δ (σ ⇒ τ)

data DTerm (Δ : Context) (τ : DType) where
  dval :
    DSVal Δ τ →
    DTerm Δ τ
  -- constants aka. primitives
  dconst :
    (c : Const τ) →
    DTerm Δ τ
  dapp : ∀ {σ}
    (dvs : DSVal Δ (σ ⇒ τ)) →
    (vt : SVal Δ σ) →
    (dvt : DSVal Δ σ) →
    DTerm Δ τ
  dlett : ∀ {σ}
    (s : Term Δ σ) →
    (ds : DTerm Δ σ) →
    (dt : DTerm (σ • Δ) τ) →
    DTerm Δ τ

derive-dvar : ∀ {Δ σ} → (x : Var Δ σ) → Var (ΔΔ Δ) (Δτ σ)
derive-dvar this = this
derive-dvar (that x) = that (derive-dvar x)

derive-dterm : ∀ {Δ σ} → (t : Term Δ σ) → DTerm Δ σ

derive-dsval : ∀ {Δ σ} → (t : SVal Δ σ) → DSVal Δ σ
derive-dsval (var x) = dvar (derive-dvar x)

derive-dsval (abs t) = dabs (derive-dterm t)

derive-dterm (val x) = dval (derive-dsval x)
derive-dterm (const c) = dconst c
derive-dterm (app vs vt) = dapp (derive-dsval vs) vt (derive-dsval vt)
derive-dterm (lett s t) = dlett s (derive-dterm s) (derive-dterm t)

-- Nontrivial because of unification problems in pattern matching. I wanted to
-- use it to define ⊕ on closures purely on terms of the closure change.

-- Instead, I decided to use decidable equality on contexts: that's a lot of
-- tedious boilerplate, but not too hard, but the proof that validity and ⊕
-- agree becomes easier.
-- -- Define a DVar and be done?
-- underive-dvar :  ∀ {Δ σ} → Var (ΔΔ Δ) (Δτ σ) → Var Δ σ
-- underive-dvar {∅} ()
-- underive-dvar {τ • Δ} x = {!!}

--underive-dvar {σ • Δ} (that x) = that (underive-dvar x)

data DVal : Type → Set
import Base.Denotation.Environment DType DVal as D

ChΔ : ∀ (Δ : Context) → Set
ChΔ Δ = D.⟦ Δ ⟧Context

data DVal where
  bang : ∀ {τ} → Val τ → DVal τ
  dclosure : ∀ {Γ σ τ} → (dt : DTerm (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) →  (dρ : ChΔ Γ) → DVal (σ ⇒ τ)
  dnatV : ∀ (n : ℕ) → DVal nat

_⊕_ : ∀ {τ} → (v1 : Val τ) (dv : DVal τ) → Val τ

_⊕ρ_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΔ Γ → ⟦ Γ ⟧Context
∅ ⊕ρ ∅ = ∅
(v • ρ1) ⊕ρ (dv • dρ) = v ⊕ dv • ρ1 ⊕ρ dρ

v1 ⊕ bang v2 = v2
closure {Γ} t ρ ⊕ dclosure {Γ1} dt ρ₁ dρ with Γ ≟Ctx Γ1
closure {Γ} t ρ ⊕ dclosure {.Γ} dt ρ₁ dρ | yes refl = closure t (ρ ⊕ρ dρ)
... | no ¬p = closure t ρ
_⊕_ (natV n) (dnatV dn) = natV (n + dn)

data _D_⊢_↓_ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) : ∀ {τ} → DTerm Γ τ → DVal τ → Set where
  dabs : ∀ {σ τ} {dt : DTerm (σ • Γ) τ} →
    ρ D dρ ⊢ dval (dabs dt) ↓ dclosure dt ρ dρ
  dvar : ∀ {τ} (x : DC.Var Γ τ) →
    ρ D dρ ⊢ dval (dvar (derive-dvar x)) ↓ D.⟦ x ⟧Var dρ
  dlit : ∀ n →
    ρ D dρ ⊢ dconst (lit n) ↓ dnatV 0
  dapp : ∀ {hasIdx} {n : Idx hasIdx}
    {Γ′ σ τ ρ′ dρ′}
    {dvs} {vt} {dvt}
    {vtv} {dvtv}
    {dt : DTerm (σ • Γ′) τ} {dv} →
    ρ D dρ ⊢ dval dvs ↓ dclosure dt ρ′ dρ′ →
    ρ ⊢ val vt ↓[ n ] vtv →
    ρ D dρ ⊢ dval dvt ↓ dvtv →
    (vtv • ρ′) D (dvtv • dρ′) ⊢ dt ↓ dv →
    ρ D dρ ⊢ dapp dvs vt dvt ↓ dv
  dlett : ∀ {hasIdx} {n : Idx hasIdx}
    {σ τ} {s : Term Γ σ} {ds} {dt : DTerm (σ • Γ) τ}
    {vsv dvsv dv} →
    ρ ⊢ s ↓[ n ] vsv →
    ρ D dρ ⊢ ds ↓ dvsv →
    (vsv • ρ) D (dvsv • dρ) ⊢ dt ↓ dv →
    ρ D dρ ⊢ dlett s ds dt ↓ dv
  bangapp : ∀ {hasIdx} {n1 n2 : Idx hasIdx}
    {Γ′ σ τ ρ′}
    {dvs} {vt} {dvt}
    {vtv2}
    {t : Term (σ • Γ′) τ} {v2} →
    ρ D dρ ⊢ dval dvs ↓ bang (closure t ρ′) →
    (ρ ⊕ρ dρ) ⊢ val vt ↓[ n1 ] vtv2 →
    (vtv2 • ρ′) ⊢ t ↓[ n2 ] v2 →
    ρ D dρ ⊢ dapp dvs vt dvt ↓ bang v2

mutual
  rrelT3 : ∀ {τ Γ} (t1 : Term Γ τ) (dt : DTerm Γ τ) (t2 : Term Γ τ) (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
  rrelT3 {τ} t1 dt t2 ρ1 dρ ρ2 k =
    (v1 v2 : Val τ) →
    ∀ j (j<k : j < k) →
    (ρ1⊢t1↓[j]v1 : ρ1 ⊢ t1 ↓[ i' j ] v1) →
    (ρ2⊢t2↓[n2]v2 : ρ2 ⊢ t2 ↓[ no ] v2) →
    Σ[ dv ∈ DVal τ ]
    ρ1 D dρ ⊢ dt ↓ dv ×
    rrelV3 τ v1 dv v2 (k ∸ j)

  rrelV3 : ∀ τ (v1 : Val τ) (dv : DVal τ) (v2 : Val τ) → ℕ → Set
  -- Making this case first ensures rrelV3 splits on its second argument, hence
  -- that all its equations hold definitionally.
  rrelV3 τ v1 (bang v2) v2' n = v2 ≡ v2'
  rrelV3 nat (natV v1) (dnatV dv) (natV v2) n = dv + v1 ≡ v2
  rrelV3 (σ ⇒ τ) (closure {Γ1} t1 ρ1) (dclosure {ΔΓ} dt ρ dρ) (closure {Γ2} t2 ρ2) n =
      Σ ((Γ1 ≡ Γ2) × (Γ1 ≡ ΔΓ)) λ { (refl , refl) →
        ρ1 ≡ ρ ×
        ρ1 ⊕ρ dρ ≡ ρ2 ×
        t1 ≡ t2 ×
        dt ≡ derive-dterm t1 ×
        ∀ (k : ℕ) (k<n : k < n) v1 dv v2 →
        rrelV3 σ v1 dv v2 k →
        rrelT3
          t1
          dt
          t2
          (v1 • ρ1)
          (dv • dρ)
          (v2 • ρ2)
          k
      }

rrelV3→⊕ : ∀ {τ n} v1 dv v2 → rrelV3 τ v1 dv v2 n → v1 ⊕ dv ≡ v2
rrelV3→⊕ v1 (bang v2) v2' vv = vv
rrelV3→⊕ (closure {Γ} t ρ) (dclosure .(derive-dterm t) .ρ dρ) (closure .t .(ρ ⊕ρ dρ)) ((refl , refl) , refl , refl , refl , refl , dvv) with Γ ≟Ctx Γ | ≟Ctx-refl Γ
... | .(yes refl) | refl = refl
rrelV3→⊕ (natV n) (dnatV dn) (natV .(dn + n)) refl rewrite +-comm n dn = refl

rrelρ3 : ∀ Γ (ρ1 : ⟦ Γ ⟧Context) (dρ : ChΔ Γ) (ρ2 : ⟦ Γ ⟧Context) → ℕ → Set
rrelρ3 ∅ ∅ ∅ ∅ n = ⊤
rrelρ3 (τ • Γ) (v1 • ρ1) (dv • dρ) (v2 • ρ2) n = rrelV3 τ v1 dv v2 n × rrelρ3 Γ ρ1 dρ ρ2 n

rrelρ3→⊕ : ∀ {Γ n} ρ1 dρ ρ2 → rrelρ3 Γ ρ1 dρ ρ2 n → ρ1 ⊕ρ dρ ≡ ρ2
rrelρ3→⊕ ∅ ∅ ∅ tt = refl
rrelρ3→⊕ (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , ρρ) rewrite rrelV3→⊕ v1 dv v2 vv | rrelρ3→⊕ ρ1 dρ ρ2 ρρ = refl

rrelV3-mono : ∀ m n → m ≤ n → ∀ τ v1 dv v2 → rrelV3 τ v1 dv v2 n → rrelV3 τ v1 dv v2 m
rrelV3-mono m n m≤n τ v1 (bang v2) v2′ vv = vv
rrelV3-mono m n m≤n (σ ⇒ τ) (closure t ρ) (dclosure dt ρ₁ dρ) (closure t₁ ρ₂)
  -- Validity
  ((refl , refl) , refl , refl , refl , refl , vv) =
  (refl  , refl) , refl , refl , refl , refl , λ k k<m → vv k (≤-trans k<m m≤n)
rrelV3-mono m n m≤n nat (natV n₁) (dnatV n₂) (natV n₃) vv = vv

rrelρ3-mono : ∀ m n → m ≤ n → ∀ Γ ρ1 dρ ρ2 → rrelρ3 Γ ρ1 dρ ρ2 n → rrelρ3 Γ ρ1 dρ ρ2 m
rrelρ3-mono m n m≤n ∅ ∅ ∅ ∅ tt = tt
rrelρ3-mono m n m≤n (τ • Γ) (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , ρρ) = rrelV3-mono m n m≤n _ v1 dv v2 vv , rrelρ3-mono m n m≤n Γ ρ1 dρ ρ2 ρρ

lt1 : ∀ {k n} → k < n → k ≤ n
lt1 (s≤s p) = ≤-step p

⟦_⟧RelVar3 : ∀ {Γ τ n} (x : Var Γ τ) {ρ1 dρ ρ2} →
  rrelρ3 Γ ρ1 dρ ρ2 n →
  rrelV3 τ (⟦ x ⟧Var ρ1) (D.⟦ x ⟧Var dρ) (⟦ x ⟧Var ρ2) n
⟦ this ⟧RelVar3   {v1 • ρ1} {dv • dρ} {v2 • ρ2} (vv , ρρ) = vv
⟦ that x ⟧RelVar3 {v1 • ρ1} {dv • dρ} {v2 • ρ2} (vv , ρρ) = ⟦ x ⟧RelVar3 ρρ

m∸n≤m : ∀ m n → m ∸ n ≤ m
m∸n≤m m zero = ≤-refl
m∸n≤m zero (suc n) = z≤n
m∸n≤m (suc m) (suc n) = ≤-step (m∸n≤m m n)

rfundamentalV3 : ∀ {Γ τ} (x : Var Γ τ) → (n : ℕ) → ∀ ρ1 dρ ρ2 (ρρ : rrelρ3 Γ ρ1 dρ ρ2 n) → rrelT3 (val (var x)) (dval (dvar (derive-dvar x))) (val (var x)) ρ1 dρ ρ2 n
rfundamentalV3 x n ρ1 dρ ρ2 ρρ .(⟦ x ⟧Var ρ1) .(⟦ x ⟧Var ρ2) .1 j<n (var .x) (var .x) =
  D.⟦ x ⟧Var dρ , dvar x , rrelV3-mono (n ∸ 1) n (m∸n≤m n 1) _ (⟦ x ⟧Var ρ1) (D.⟦ x ⟧Var dρ) (⟦ x ⟧Var ρ2) (⟦ x ⟧RelVar3 ρρ)

suc∸ : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
suc∸ m zero z≤n = refl
suc∸ (suc m) (suc n) (s≤s n≤m) = suc∸ m n n≤m

sub∸ : ∀ m n o → m + n ≤ o → n ≤ o ∸ m
sub∸ m n o n+m≤o rewrite +-comm m n | cong (_≤ o ∸ m) (sym (m+n∸n≡m n m)) = ∸-mono n+m≤o (≤-refl {m})

-- Warning: names like ρ1⊢t1↓[j]v1 are all broken, sorry for not fixing them.
rfundamental3 : ∀ {τ Γ} k (t : Term Γ τ) → ∀ ρ1 dρ ρ2 → (ρρ : rrelρ3 Γ ρ1 dρ ρ2 k) →
  rrelT3 t (derive-dterm t) t ρ1 dρ ρ2 k
rfundamental3 k (val (var x)) ρ1 dρ ρ2 ρρ = rfundamentalV3 x k ρ1 dρ ρ2 ρρ
rfundamental3 (suc k) (val (abs t)) ρ1 dρ ρ2 ρρ .(closure t ρ1) .(closure t ρ2) .1 (s≤s j<k) abs abs =
  dclosure (derive-dterm t) ρ1 dρ , dabs , (refl , refl) , refl , rrelρ3→⊕ ρ1 dρ ρ2 ρρ , refl , refl ,
    λ k₁ k<n v1 dv v2 vv v3 v4 j j<k₁ ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2 →
    rfundamental3 k₁ t (v1 • ρ1) (dv • dρ) (v2 • ρ2) (vv , rrelρ3-mono k₁ (suc k) (≤-step (lt1 k<n)) _ _ _ _ ρρ) v3 v4 j j<k₁ ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
rfundamental3 k (const .(lit n)) ρ1 dρ ρ2 ρρ (natV n) .(natV n) .1 j<k (lit .n) (lit .n) = dnatV 0 , dlit n , refl
rfundamental3 (suc (suc (suc (suc k)))) (app vs vt) ρ1 dρ ρ2 ρρ v1 v2 .(suc (suc (suc j))) (s≤s (s≤s (s≤s (s≤s j<k))))
  (app j vtv1 ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2 ρ1⊢t1↓[j]v3)
  (app n₁ vtv2 ρ2⊢t2↓[n2]v2 ρ2⊢t2↓[n2]v3 ρ2⊢t2↓[n2]v4)
  with rfundamental3 (suc (suc (suc (suc k)))) (val vs) ρ1 dρ ρ2 ρρ _ _ (suc zero) (s≤s (s≤s z≤n)) ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
       | rfundamental3 (suc (suc (suc (suc k)))) (val vt) ρ1 dρ ρ2 ρρ _ _ (suc zero) (s≤s (s≤s z≤n)) ρ1⊢t1↓[j]v2 ρ2⊢t2↓[n2]v3
... | bang f2 , vs↓dsv , refl | dtv , vt↓dvv , dtvv
      rewrite sym (rrelρ3→⊕ ρ1 dρ ρ2 ρρ) =
        bang v2 , bangapp vs↓dsv ρ2⊢t2↓[n2]v3 ρ2⊢t2↓[n2]v4 , refl
... | dclosure dt ρ dρ₁ , vs↓dsv , (refl , refl) , refl , refl , refl , refl , dsvv | dtv , vt↓dvv , dtvv
      with dsvv (suc k) (s≤s (s≤s (≤-step ≤-refl))) vtv1 dtv vtv2
           ( (rrelV3-mono (suc k) (suc (suc (suc k))) (s≤s (≤-step (≤-step ≤-refl))) _ vtv1 dtv vtv2 dtvv) )
           v1 v2 j (s≤s j<k) ρ1⊢t1↓[j]v3 ρ2⊢t2↓[n2]v4
... | dv , ↓dv , dvv =
      dv , dapp vs↓dsv ρ1⊢t1↓[j]v2 vt↓dvv ↓dv , dvv
rfundamental3 (suc (suc k)) (lett s t) ρ1 dρ ρ2 ρρ v1 v2 .(suc (n1 + n2)) (s≤s (s≤s n1+n2≤k))
  (lett n1 n2 vs1 .s .t ρ1⊢t1↓[j]v1 ρ1⊢t1↓[j]v2) (lett _ _ vs2 .s .t ρ2⊢t2↓[n2]v2 ρ2⊢t2↓[n2]v3)
  with rfundamental3 (suc (suc k)) s ρ1 dρ ρ2 ρρ vs1 vs2 n1
    (s≤s (≤-trans (≤-trans (m≤m+n n1 n2) n1+n2≤k) (≤-step ≤-refl)))
    ρ1⊢t1↓[j]v1 ρ2⊢t2↓[n2]v2
... | dsv , ↓dsv , vsv
      with rfundamental3 (suc (suc k) ∸ n1) t (vs1 • ρ1) (dsv • dρ) (vs2 • ρ2) (vsv , rrelρ3-mono (suc (suc k) ∸ n1) (suc (suc k)) (m∸n≤m (suc (suc k)) n1) _ _ _ _ ρρ) v1 v2 n2 (sub∸ n1 (suc n2) (suc (suc k)) n1+[1+n2]≤2+k) ρ1⊢t1↓[j]v2 ρ2⊢t2↓[n2]v3
      where
        n1+[1+n2]≤2+k : n1 + suc n2 ≤ suc (suc k)
        n1+[1+n2]≤2+k rewrite +-suc n1 n2 = ≤-step (s≤s n1+n2≤k)
... | dv , ↓dv , dvv = dv , dlett ρ1⊢t1↓[j]v1 ↓dsv ↓dv , rrelV3-mono (suc k ∸ (n1 + n2)) (suc (suc k) ∸ n1 ∸ n2) 1+k-[n1+n2]≤2+k-n1-n2 _ v1 dv v2 dvv
  where
    1+k-[n1+n2]≤2+k-n1-n2 : suc k ∸ (n1 + n2) ≤ suc (suc k) ∸ n1 ∸ n2
    1+k-[n1+n2]≤2+k-n1-n2 rewrite ∸-+-assoc (suc (suc k)) n1 n2 = ∸-mono {suc k} {suc (suc k)} {n1 + n2} {n1 + n2} (≤-step ≤-refl) ≤-refl
