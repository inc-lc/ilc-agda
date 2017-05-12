{-# OPTIONS --allow-unsolved-metas #-}
module Thesis.BigStep where

open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Binary hiding (_⇒_)
open import Data.Nat using (ℕ; zero; suc; decTotalOrder; _<_)

open import Thesis.Syntax hiding (suc)
open import Thesis.Lang hiding (⟦_⟧Context; ⟦_⟧Var; suc)

-- open import Base.Syntax.Context Type public
-- open import Base.Syntax.Vars Type public

-- data Const : (τ : Type) → Set where
--   lit : ℤ → Const int
--   -- succ : Const (int ⇒ int)

-- data Term (Γ : Context) :
--   (τ : Type) → Set where
--   -- constants aka. primitives
--   const : ∀ {τ} →
--     (c : Const τ) →
--     Term Γ τ
--   var : ∀ {τ} →
--     (x : Var Γ τ) →
--     Term Γ τ
--   app : ∀ {σ τ}
--     (s : Term Γ (σ ⇒ τ)) →
--     (t : Term Γ σ) →
--     Term Γ τ
--   -- we use de Bruijn indices, so we don't need binding occurrences.
--   abs : ∀ {σ τ}
--     (t : Term (σ • Γ) τ) →
--     Term Γ (σ ⇒ τ)

data Val : Type → Set
open import Base.Denotation.Environment Type Val public
open import Base.Data.DependentList public

data Val where
  closure : ∀ {Γ σ τ} → (t : Term (σ • Γ) τ) → (ρ : ⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  intV : ∀ (n : ℤ) → Val int
  -- prim : ∀ {σ τ} → (f : Val σ → Val τ) → Val (σ ⇒ τ)
  -- prim : ∀ {σ τ} → (f : ⟦ σ ⇒ τ ⟧Type) → Val (σ ⇒ τ)
  pairV : ∀ {σ τ} → Val σ → Val τ → Val (pair σ τ)
  -- prim : ∀ {σ τ} → (f : ⟦ σ ⟧Type → Val τ) → Val (σ ⇒ τ)

-- TODO: add defunctionalized interpretations for primitives. Yes, annoying but mechanical.

-- Doesn't work
-- data Val2 : ℕ → Type → Set where
--   prim : ∀ {σ τ n} → (f : Val2 n σ → Val2 n τ) → Val2 (ℕ.suc n) (σ ⇒ τ)

import Base.Denotation.Environment
-- Den stands for Denotational semantics.
module Den = Base.Denotation.Environment Type ⟦_⟧Type

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → ⟦ Γ ⟧Context → Den.⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Term) (v • ⟦ ρ ⟧Env)
⟦ intV n ⟧Val = n
-- ⟦ prim f ⟧Val = λ v → ⟦ f v ⟧Val
⟦ pairV a b ⟧Val = (⟦ a ⟧Val , ⟦ b ⟧Val)
-- ⟦ true ⟧Val = true
-- ⟦ false ⟧Val = false

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  Den.⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ ⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

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
evalConst c n = {!!}

-- evalConst plus n = Done (prim (λ a → prim (λ b → intV (a + b))))
-- evalConst minus n = Done (prim (λ a → prim (λ b → intV (a - b))))
-- evalConst cons n = Done (prim (λ a → prim (λ b → {!pairV !})))
-- evalConst fst n = {!!}
-- evalConst snd n = {!!}
-- evalConst linj n = {!!}
-- evalConst rinj n = {!!}
-- evalConst match n = {!!}
-- evalConst zero = intV (+ 0)
-- evalConst succ = {!!}

eval : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure t ρ) a n = eval t (a • ρ) n
-- apply (prim f) a n = Done (f ⟦ a ⟧Val)

eval t ρ zero = TimeOut
eval (const c) ρ (suc n) = evalConst c n
eval (var x) ρ (suc n) = Done (⟦ x ⟧Var ρ)
eval (abs t) ρ (suc n) = Done (closure t ρ)
eval (app s t) ρ (suc n) with eval s ρ n | eval t ρ n
... | Done f | Done a = apply f a n
... | _ | _ = TimeOut
-- eval t0 ρ (suc n) with t0
-- ... | const c = evalConst c n
-- ... | var x = Done (⟦ x ⟧Var ρ)
-- ... | abs t = Done (closure t ρ)
-- ... | app s t with eval s ρ n | eval t ρ n
-- ... | Done f | Done a = apply f a n
-- ... | _ | _ = TimeOut

-- Can we prove eval sound wrt. our reference denotational semantics? Yes! Very
-- cool!
eval-sound : ∀ {Γ τ} ρ v n (t : Term Γ τ) →
  eval t ρ n ≡ Done v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

apply-sound : ∀ {Γ σ τ} ρ v f a n (s : Term Γ (σ ⇒ τ)) t →
  ⟦ s ⟧Term ⟦ ρ ⟧Env ≡ ⟦ f ⟧Val →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ a ⟧Val →
  apply f a n ≡ Done v →
  ⟦ s ⟧Term ⟦ ρ ⟧Env (⟦ t ⟧Term ⟦ ρ ⟧Env) ≡ ⟦ v ⟧Val
apply-sound _ v (closure ft ρ) a n s t feq aeq eq rewrite feq | aeq = eval-sound (a • ρ) v n ft eq

eval-sound ρ v zero t ()
eval-sound ρ v (ℕ.suc n) (const c) eq = {!!}
eval-sound ρ v (ℕ.suc n) (var x) refl = ↦-sound ρ x
eval-sound ρ v (ℕ.suc n) (abs t) refl = refl
eval-sound ρ v (ℕ.suc n) (app s t) eq with eval s ρ n | inspect (eval s ρ) n | eval t ρ n | inspect (eval t ρ) n
eval-sound ρ v (ℕ.suc n) (app s t) eq | Done f | [ feq ] | Done a | [ aeq ] =
  let feq = eval-sound ρ f n s feq; aeq = eval-sound ρ a n t aeq in apply-sound ρ v f a n s t feq aeq eq
eval-sound ρ v (ℕ.suc n) (app s t) () | Done f | _ | TimeOut | _
eval-sound ρ v (ℕ.suc n) (app s t) () | TimeOut | _ | _ | _
-- eval-sound n (const c) eq = {!!}
-- eval-sound n (var x) eq = {!!}
-- eval-sound n (app s t) eq = {!!} -- with eval s ρ n
-- eval-sound n (abs t) eq = {!!}
-- eval-sound n (const c) eq = {!!}
-- eval-sound n (var x) eq = {!!}
-- eval-sound n (app s t) eq = {!!} -- with eval s ρ n
-- eval-sound n (abs t) eq = {!!}

-- Next, we can try defining change structures and validity.

dapply : ∀ {σ τ} → Val (Δt (σ ⇒ τ)) → Val σ → Val (Δt σ) → Res (Δt τ)
dapply df a1 da zero = TimeOut
dapply df a1 da (suc zero) = TimeOut
dapply df a1 da (suc (suc n)) with apply df a1 n
... | Done dfa = apply dfa da (suc n)
... | TimeOut = TimeOut

-- apply (closure (abs (derive t)) dρ) a1 (suc (suc n))
-- eval (derive (abs t)) dρ (suc n) ≡
-- dapply-sound-0
--   dapply (closure (abs (derive t)) dρ) a1 da (suc n) ≡
--   eval (derive t) (da • a1 • dρ) n

dapply' : ∀ {σ τ} → ErrVal (Δt (σ ⇒ τ)) → ErrVal σ → ErrVal (Δt σ) → Res (Δt τ)
dapply' (Done df) (Done v) (Done dv) n = dapply df v dv n
dapply' _ _ _ _ = TimeOut

-- Which step-indexes should we use in dapply's specification and
-- implementation? That's highly non-obvious. To come up with them, I had to
-- step through the evaluation of eval (app (app ds t) dt), and verify that I
-- never invoke eval or apply on the same inputs at different step-indexes.
--
-- However, I expect I wouldn't be able to get a working proof if I got the
-- indexes wrong.
dapply-sound : ∀ {Γ σ τ} n ρ (ds : Term Γ (Δt (σ ⇒ τ))) t dt →
    eval (app (app ds t) dt) ρ (suc (suc n))
  ≡
    dapply' (eval ds ρ n) (eval t ρ n) (eval dt ρ (suc n)) (suc (suc n))
dapply-sound zero ρ ds t dt = refl
dapply-sound (suc n) ρ ds t dt with
  eval ds ρ (suc n) | eval t ρ (suc n) | eval dt ρ (suc (suc n))
dapply-sound (suc n) ρ ds t dt | Done df | Done v | Done dv with apply df v (suc n)
... | Done dfv = refl
... | TimeOut  = refl
dapply-sound (suc n) ρ ds t dt | Done df | Done v | TimeOut with apply df v (suc n)
... | Done dfv = refl
... | TimeOut = refl
dapply-sound (suc n) ρ ds t dt | Done df | TimeOut | dv = refl
dapply-sound (suc n) ρ ds t dt | TimeOut | v | dv = refl

ΔΓ : Context → Context
ΔΓ ∅ = ∅
ΔΓ (τ • Γ) = Δt τ • τ • ΔΓ Γ

ChΓ : ∀ (Γ : Context) → Set
ChΓ Γ = ⟦ ΔΓ Γ ⟧Context
Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔΓ Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop Δt τ • keep τ • Γ≼ΔΓ

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔΓ Γ) τ
fit = weaken Γ≼ΔΓ

deriveConst : ∀ {τ} →
  Const τ →
  Term ∅ (Δt τ)
deriveConst = {!!}

derive-var : ∀ {Γ τ} → Var Γ τ → Var (ΔΓ Γ) (Δt τ)
derive-var this = this
derive-var (that x) = that (that (derive-var x))

derive : ∀ {Γ τ} → Term Γ τ → Term (ΔΓ Γ) (Δt τ)
derive (const c) = weaken (∅≼Γ {ΔΓ _}) (deriveConst c)
derive (var x) = var (derive-var x)
derive (app s t) = app (app (derive s) (fit t)) (derive t)
derive (abs t) = abs (abs (derive t))


-- open import Thesis.Derive
Chτ : Type → Set
Chτ τ = Val (Δt τ)

deval : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Res (Δt τ)
deval t ρ dρ = eval (derive t) dρ


dapply-equiv : ∀ {Γ σ τ} n
  (t : Term (σ • Γ) τ)
  (dρ : ChΓ Γ) (ρ1 : ⟦ Γ ⟧Context)
  (da : Val (Δt σ)) (a1 : Val σ) →
  dapply (closure (abs (derive t)) dρ) a1 da (suc (suc (suc n))) ≡
  eval (derive t) (da • a1 • dρ) (suc (suc n))
dapply-equiv n t dρ ρ1 da a1 = refl

-- Target statement:

_[_]τ_from_to_ : (n : ℕ) → ∀ τ → Val (Δt τ) → Val τ → Val τ → Set
_[_]τ'_from_to_ : (n : ℕ) → ∀ τ → ErrVal (Δt τ) → ErrVal τ → ErrVal τ → Set
n [ τ ]τ' Done dv from Done v1 to Done v2 = n [ τ ]τ dv from v1 to v2
n [ τ ]τ' TimeOut from Done v1 to Done v2 = ⊥
n [ τ ]τ' dv from _ to _ = ⊤

-- XXX: This is a lie for now, but all papers agree we'll want this in the end.
_[_]τmono_from_to : (n : ℕ) → ∀ τ → (dv : Val (Δt τ)) →
  ∀ v1 v2 n' →
  n' < n →
  n [ τ ]τ dv from v1 to v2 →
  n' [ τ ]τ dv from v1 to v2
_[_]τmono_from_to = {!!}


_[_]τ'_fromToTimeOut : ∀ n τ edv → n [ τ ]τ' edv from TimeOut to TimeOut ≡ ⊤
n [ τ ]τ' Done v fromToTimeOut = refl
n [ τ ]τ' TimeOut fromToTimeOut = refl
-- n [ τ ]τ' dv from Done v1 to TimeOut = ⊤
-- n [ τ ]τ' dv from TimeOut to Done v2 = ⊤
-- n [ τ ]τ' dv from TimeOut to TimeOut = ⊤

-- In the static-caching paper, the specification we use is similar to this one:
-- n [ σ ⇒ τ ]τ df from f1 to f2 = ∀ (da : Val (Δt σ)) → (a1 a2 : Val σ) →
--    n [ σ ]τ da from a1 to a2 →
--    ∀ v1 v2 → apply f1 a1 n ≡ Done v1 → apply f2 a2 n ≡ Done v2 →
--    Σ[ dv ∈ Val (Δt τ) ]
--        dapply df a1 da n ≡ Done dv
--      × n [ τ ]τ dv from v1 to v2
-- I defined _[_]τ'_from_to_ to be able to write an equivalent (hopefully) specification more quickly.

zero [ τ ]τ dv from v1 to v2 = ⊤
-- suc n [ σ ⇒ τ ]τ df from f1 to f2 =
--   ∀ (da : Val (Δt σ)) → (a1 a2 : Val σ) →
--    n [ σ ]τ da from a1 to a2 →
--    n [ τ ]τ' dapply df a1 da n from apply f1 a1 n to apply f2 a2 n

suc n [ σ ⇒ τ ]τ df from f1 to f2 = ∀ (da : Val (Δt σ)) → (a1 a2 : Val σ) →
   suc n [ σ ]τ da from a1 to a2 →

-- This definition violates all tips from Pitts tutorial (Step-Indexed
-- Biorthogonality: a Tutorial Example). Compare with Definition 4.1,
-- equation (10), and remark 4.4.
--
-- For extra complication, the setting is rather different, so a direct
-- comparison doesn't quite work.
   ∀ v1 v2 → apply f1 a1 (suc n) ≡ Done v1 → apply f2 a2 (suc n) ≡ Done v2 →
   Σ[ dv ∈ Val (Δt τ) ]
       dapply df a1 da (suc (suc n)) ≡ Done dv
     × n [ τ ]τ dv from v1 to v2

suc n [ int ]τ intV dn from intV n1 to intV n2 = n1 + dn ≡ n2
suc n [ pair σ τ ]τ pairV da db from pairV a1 b1 to pairV a2 b2 =
  suc n [ σ ]τ da from a1 to a2 × suc n [ τ ]τ db from b1 to b2
suc n [ sum σ τ ]τ () from v1 to v2

data _[_]Γ_from_to_ : ∀ ℕ Γ → ChΓ Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set where
  v∅ : ∀ {n} → n [ ∅ ]Γ ∅ from ∅ to ∅
  _v•_ : ∀ {n τ Γ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : n [ τ ]τ dv from v1 to v2) →
    (dρρ : n [ Γ ]Γ dρ from ρ1 to ρ2) →
    n [ τ • Γ ]Γ (dv • v1 • dρ) from (v1 • ρ1) to (v2 • ρ2)

fromtoDeriveVar : ∀ {Γ} τ n → (x : Var Γ τ) →
  (dρ : ChΓ Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context) → n [ Γ ]Γ dρ from ρ1 to ρ2 →
    n [ τ ]τ (⟦ derive-var x ⟧Var dρ) from ⟦ x ⟧Var ρ1 to ⟦ x ⟧Var ρ2
fromtoDeriveVar τ n this (dv • .(v1 • _)) (v1 • ρ1) (v2 • ρ2) (dvv v• dρρ) = dvv
fromtoDeriveVar τ n (that x) (dv • (.v1 • dρ)) (v1 • ρ1) (v2 • ρ2) (dvv v• dρρ) = fromtoDeriveVar τ n x dρ ρ1 ρ2 dρρ

foo : ∀ {Γ σ τ v1 v2 dv} n (t : Term (σ • Γ) τ) →
  (dρ : ChΓ Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context)
  (da : Val (Δt σ)) (a1 a2 : Val σ) →
  (eqv1 : eval t (a1 • ρ1) (suc (suc n)) ≡ Done v1) →
  (eqv2 : eval t (a2 • ρ2) (suc (suc n)) ≡ Done v2) →
  (eqvv : eval (derive t) (da • a1 • dρ) (suc (suc n)) ≡ Done dv) →
  suc (suc n) [ τ ]τ' eval (derive t) (da • a1 • dρ) (suc (suc n)) from
      eval t (a1 • ρ1) (suc (suc n)) to eval t (a2 • ρ2) (suc (suc n)) →
  suc n [ τ ]τ dv from v1 to v2
foo n t dρ ρ1 ρ2 da a1 a2 eqv1 eqv2 eqvv dvv with eval t (a1 • ρ1) (suc (suc n)) | eval t (a2 • ρ2) (suc (suc n)) | eval (derive t) (da • a1 • dρ) (suc (suc n))
foo n t dρ ρ1 ρ2 da a1 a2 refl refl refl dvv | Done v1 | (Done v2) | (Done dv) = _[_]τmono_from_to (suc (suc n)) _ dv v1 v2 (suc n) (DecTotalOrder.reflexive Data.Nat.decTotalOrder refl) dvv
foo n t dρ ρ1 ρ2 da a1 a2 refl refl () dvv | Done v₁ | (Done v) | TimeOut
foo n t dρ ρ1 ρ2 da a1 a2 refl () eqvv dvv | Done v | TimeOut | s
foo n t dρ ρ1 ρ2 da a1 a2 () eqv2 eqvv dvv | TimeOut | r | s
-- q r s eqv1 eqv2 eqvv

fromtoDerive : ∀ {Γ} τ n → (t : Term Γ τ) →
  (dρ : ChΓ Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context) → n [ Γ ]Γ dρ from ρ1 to ρ2 →
    n [ τ ]τ' (deval t ρ1 dρ n) from eval t ρ1 n to eval t ρ2 n
fromtoDerive τ zero t dρ ρ1 ρ2 dρρ rewrite zero [ τ ]τ' (deval t ρ1 dρ (suc zero)) fromToTimeOut = tt
fromtoDerive τ (suc n) (const c) dρ ρ1 ρ2 dρρ = {!!}
fromtoDerive τ (suc n) (var x) dρ ρ1 ρ2 dρρ = fromtoDeriveVar τ (suc n) x dρ ρ1 ρ2 dρρ
fromtoDerive τ (suc n) (app s t) dρ ρ1 ρ2 dρρ = {!fromtoDerive _ (suc n) s dρ ρ1 ρ2 dρρ!}
-- fromtoDerive (σ ⇒ τ) (suc n) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa
--   rewrite dapply-equiv n t dρ ρ1 da a1 =
--   fromtoDerive τ (suc n) t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) (daa v• dρρ)
fromtoDerive (σ ⇒ τ) (suc zero) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa v1 v2 eqv1 eqv2 = {!LIE!!}
fromtoDerive (σ ⇒ τ) (suc (suc n)) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa v1 v2 eqv1 eqv2 with
  eval (derive t) (da • a1 • dρ) (suc (suc n)) | inspect (eval (derive t) (da • a1 • dρ)) (suc (suc n))
fromtoDerive (σ ⇒ τ) (suc (suc n)) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa v1 v2 eqv1 eqv2 | Done dv | [ eqvv ] = dv , refl , foo n t  dρ ρ1 ρ2 da a1 a2 eqv1 eqv2 eqvv (fromtoDerive τ (suc (suc n)) t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) (daa v• dρρ))
fromtoDerive (σ ⇒ τ) (suc (suc n)) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa v1 v2 eqv1 eqv2 | TimeOut | eq = {!LIE!!}
-- {!eval (derive t)!} , {!fromtoDerive τ (suc n) t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) ?!}

-- fromtoDerive (σ ⇒ τ) (suc (suc zero)) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa = {!!}
-- fromtoDerive (σ ⇒ τ) (suc (suc (suc n))) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa
--   with eval (abs (derive t)) (a1 • dρ) n | inspect (eval (abs (derive t)) (a1 • dρ)) n
-- fromtoDerive (σ ⇒ τ) (suc (suc (suc n))) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa | Done v | [ eq ] = {!fromtoDerive τ (suc (suc n)) t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) _!}
-- fromtoDerive (σ ⇒ τ) (suc (suc (suc n))) (abs t) dρ ρ1 ρ2 dρρ da a1 a2 daa | TimeOut | _ = {!!}
-- --   fromtoDerive τ n t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) (daa v• ?)
-- -- fromtoDerive τ (suc (suc n)) t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) {! daa v• dρρ!}
--   -- fromtoDerive τ n t (da • a1 • dρ) (a1 • ρ1) (a2 • ρ2) {! daa v• dρρ!}
