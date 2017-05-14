--
-- Formalize correctness of differentiation for the source calculus in the
-- static caching paper (typed version).
--

module Thesis.ANormal where

open import Thesis.Types public
open import Thesis.Contexts public

open import Relation.Binary.PropositionalEquality

data Term (Γ : Context) (τ : Type) : Set where
  var : (x : Var Γ τ) →
    Term Γ τ
  lett : ∀ {σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → Term (τ₁ • Γ) τ → Term Γ τ

weaken-term : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Term Γ₁ τ →
  Term Γ₂ τ
weaken-term Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
weaken-term Γ₁≼Γ₂ (lett f x t) = lett (weaken-var Γ₁≼Γ₂ f) (weaken-var Γ₁≼Γ₂ x) (weaken-term ( keep _ • Γ₁≼Γ₂) t)

-- Also represent top-level definitions, so that we can somehow create functions
-- via syntax. Made up on the moment.

-- WARNING: this allows nested lambdas. That's more powerful than allowing only
-- closures whose bodies can't contain lambdas, like in the paper.
data Fun (Γ : Context) : (τ : Type) → Set where
  term : ∀ {τ} → Term Γ τ → Fun Γ τ
  abs : ∀ {σ τ} → Fun (σ • Γ) τ → Fun Γ (σ ⇒ τ)

weaken-fun : ∀ {Γ₁ Γ₂ τ} →
  (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
  Fun Γ₁ τ →
  Fun Γ₂ τ
weaken-fun Γ₁≼Γ₂ (term x) = term (weaken-term Γ₁≼Γ₂ x)
weaken-fun Γ₁≼Γ₂ (abs f) = abs (weaken-fun (keep _ • Γ₁≼Γ₂) f)

open import Thesis.Environments public

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ var x ⟧Term ρ = ⟦ x ⟧Var ρ
⟦ lett f x t ⟧Term ρ = ⟦ t ⟧Term (⟦ f ⟧Var ρ (⟦ x ⟧Var ρ) • ρ)

weaken-term-sound : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂)
  (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken-term Γ₁≼Γ₂ t ⟧Term ρ ≡ ⟦ t ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-term-sound Γ₁≼Γ₂ (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
weaken-term-sound Γ₁≼Γ₂ (lett f x t) ρ rewrite
  weaken-var-sound Γ₁≼Γ₂ f ρ | weaken-var-sound Γ₁≼Γ₂ x ρ =
    weaken-term-sound
      (keep _ • Γ₁≼Γ₂)
      t
      (⟦ f ⟧Var (⟦ Γ₁≼Γ₂ ⟧≼ ρ) (⟦ x ⟧Var (⟦ Γ₁≼Γ₂ ⟧≼ ρ)) • ρ)

⟦_⟧Fun : ∀ {Γ τ} → Fun Γ τ → ⟦ Γ ⟧Context → ⟦ τ ⟧Type
⟦ term t ⟧Fun ρ = ⟦ t ⟧Term ρ
⟦ abs f ⟧Fun ρ = λ v → ⟦ f ⟧Fun (v • ρ)

open import Postulate.Extensionality

weaken-fun-sound : ∀ {Γ₁ Γ₂ τ} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂)
  (t : Fun Γ₁ τ) (ρ : ⟦ Γ₂ ⟧Context) → ⟦ weaken-fun Γ₁≼Γ₂ t ⟧Fun ρ ≡ ⟦ t ⟧Fun (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
weaken-fun-sound Γ₁≼Γ₂ (term x) ρ = weaken-term-sound Γ₁≼Γ₂ x ρ
weaken-fun-sound Γ₁≼Γ₂ (abs f) ρ = ext (λ v → weaken-fun-sound (keep _ • Γ₁≼Γ₂) f (v • ρ))

open import Thesis.Changes public
open import Thesis.LangChanges public

derive-var : ∀ {Γ τ} → Var Γ τ → Var (ΔΓ Γ) (Δt τ)
derive-var this = this
derive-var (that x) = that (that (derive-var x))

⟦_⟧ΔVar : ∀ {Γ τ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ x ⟧ΔVar ρ dρ = ⟦ derive-var x ⟧Var dρ

fromtoDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dvv v• dρρ) = dvv
fromtoDeriveVar (that x) (dvv v• dρρ) = fromtoDeriveVar x dρρ

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔΓ Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop Δt τ • keep τ • Γ≼ΔΓ

⟦Γ≼ΔΓ⟧ : ∀ {Γ ρ1 ρ2 dρ} → (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
  ρ1 ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ v∅ = refl
⟦Γ≼ΔΓ⟧ (dvv v• dρρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ dρρ)

fit-var : ∀ {τ Γ} → Var Γ τ → Var (ΔΓ Γ) τ
fit-var = weaken-var Γ≼ΔΓ

fit-var-sound : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ x ⟧Var ρ1 ≡ ⟦ fit-var x ⟧Var dρ
fit-var-sound x dρρ = trans
  (cong ⟦ x ⟧Var (⟦Γ≼ΔΓ⟧ dρρ))
  (sym (weaken-var-sound Γ≼ΔΓ x _))

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔΓ Γ) τ
fit = weaken-term Γ≼ΔΓ

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ t ⟧Term ρ1 ≡ ⟦ fit t ⟧Term dρ
fit-sound t dρρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ dρρ))
  (sym (weaken-term-sound Γ≼ΔΓ t _))

derive-term : ∀ {Γ τ} → Term Γ τ → Term (ΔΓ Γ) (Δt τ)
derive-term (var x) = var (derive-var x)
derive-term (lett f x t) =
  lett (fit-var f) (fit-var x)
    (lett (weaken-var (drop _ • ≼-refl) (derive-var f)) (weaken-var (drop _ • Γ≼ΔΓ) x) (
    lett this (weaken-var (drop _ • drop _ • ≼-refl) (derive-var x))
      (weaken-term (keep _ • drop _ • ≼-refl) (derive-term t))))

⟦_⟧ΔTerm : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ t ⟧ΔTerm ρ dρ = ⟦ derive-term t ⟧Term dρ


fromtoDeriveTerm : ∀ {Γ τ} → (t : Term Γ τ) →
  ch ⟦ t ⟧ΔTerm from ⟦ t ⟧Term to ⟦ t ⟧Term
-- You might think I'm going to prove the statement of fromtoDeriveTerm. In
-- fact, I'm going to prove that weakening is evil.
fromtoDeriveTerm (var x) dρ ρ1 ρ2 dρρ = fromtoDeriveVar x dρρ
fromtoDeriveTerm (lett f x t) dρ ρ1 ρ2 dρρ with ⟦ f ⟧Var ρ1 | inspect ⟦ f ⟧Var ρ1 | ⟦ x ⟧Var ρ1 | inspect ⟦ x ⟧Var ρ1 | ⟦ derive-var f ⟧Var dρ | inspect ⟦ derive-var f ⟧Var dρ
... | fv1 | [ fv1eq ] | xv1 | [ xv1eq ] | dfv1 | [ dfv1eq ] with fv1 xv1 | inspect fv1 xv1
... | fx1 | [ fx1eq ]
  rewrite sym (fit-var-sound f dρρ)
  | sym (fit-var-sound x dρρ)
  | fv1eq
  | xv1eq
  | fx1eq
  | weaken-var-sound (drop _ • ≼-refl) (derive-var f) (fx1 • dρ)
  | weaken-var-sound (drop _ • Γ≼ΔΓ) x (fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | sym (⟦Γ≼ΔΓ⟧ dρρ)
  | xv1eq
  | dfv1eq
  | weaken-var-sound (drop _ • drop _ • ≼-refl) (derive-var x) (dfv1 xv1 • fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | weaken-term-sound (keep _ • drop _ • ≼-refl) (derive-term t) (dfv1 xv1 (⟦ derive-var x ⟧Var dρ) • dfv1 xv1 • fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | sym dfv1eq
  | sym xv1eq
  | sym fx1eq
  | sym fv1eq
  =
  let fromToF = fromtoDeriveVar f dρρ
      fromToX = fromtoDeriveVar x dρρ
      fromToFX = fromToF (⟦ derive-var x ⟧Var dρ) _ _ fromToX
  in fromtoDeriveTerm t _ _ _ (fromToFX v• dρρ)

derive-fun : ∀ {Γ τ} → Fun Γ τ → Fun (ΔΓ Γ) (Δt τ)
derive-fun (term t) = term (derive-term t)
derive-fun (abs f) = abs (abs (derive-fun f))

⟦_⟧ΔFun : ∀ {Γ τ} → (t : Fun Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ f ⟧ΔFun ρ dρ = ⟦ derive-fun f ⟧Fun dρ

fromtoDeriveFun : ∀ {Γ τ} → (f : Fun Γ τ) →
  ch ⟦ f ⟧ΔFun from ⟦ f ⟧Fun to ⟦ f ⟧Fun
fromtoDeriveFun (term t) = fromtoDeriveTerm t
fromtoDeriveFun (abs f) dρ ρ1 ρ2 dρρ = λ dv v1 v2 dvv → fromtoDeriveFun f (dv • v1 • dρ) (v1 • ρ1) (v2 • ρ2) (dvv v• dρρ)

-- Next steps:
-- 1. Add a functional big-step semantics for this language: DONE.
-- 2. Prove it sound wrt. the denotational semantics: DONE.
-- 3. Add an erasure to a uni-typed language. DONE.
-- 4. Redo 1 with an *untyped* functional big-step semantics.
-- 5. Prove that evaluation and erasure commute:
-- -- erasure-commute-term : ∀ {Γ τ} (t : T.Term Γ τ) ρ n →
-- --   erase-errVal (T.eval-term t ρ n) ≡ eval-term (erase-term t) (erase-env ρ) n
-- 6. Define new caching transformation into untyped language.
--
-- 7. Prove the new transformation correct in the untyped language, by reusing
-- evaluation on the source language.

data Val : Type → Set
-- data Val (τ : Type) : Set

import Base.Denotation.Environment
module Op = Base.Denotation.Environment Type Val
open import Base.Data.DependentList public
open import Data.Nat.Base
open import Data.Integer

-- data Val (τ : Type) where
data Val where
  closure : ∀ {Γ σ τ} → (t : Fun (σ • Γ) τ) → (ρ : Op.⟦ Γ ⟧Context) → Val (σ ⇒ τ)
  intV : ∀ (n : ℤ) → Val int

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

eval-fun : ∀ {Γ τ} → Fun Γ τ → Op.⟦ Γ ⟧Context → Res τ
eval-term : ∀ {Γ τ} → Term Γ τ → Op.⟦ Γ ⟧Context → Res τ

apply : ∀ {σ τ} → Val (σ ⇒ τ) → Val σ → Res τ
apply (closure f ρ) a n = eval-fun f (a • ρ) n

eval-term t ρ zero = TimeOut
eval-term (var x) ρ (suc n) = Done (Op.⟦ x ⟧Var ρ)
eval-term (lett f x t) ρ (suc n) = apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n >>= (λ v → eval-term t (v • ρ) n)

eval-fun (term t) ρ n = eval-term t ρ n
eval-fun (abs f) ρ n = Done (closure f ρ)

⟦_⟧Val : ∀ {τ} → Val τ → ⟦ τ ⟧Type
⟦_⟧Env : ∀ {Γ} → Op.⟦ Γ ⟧Context → ⟦ Γ ⟧Context

⟦ ∅ ⟧Env = ∅
⟦ v • ρ ⟧Env = ⟦ v ⟧Val • ⟦ ρ ⟧Env

⟦ closure t ρ ⟧Val = λ v → (⟦ t ⟧Fun) (v • ⟦ ρ ⟧Env)
⟦ intV n ⟧Val = n

↦-sound : ∀ {Γ τ} ρ (x : Var Γ τ) →
  ⟦ x ⟧Var ⟦ ρ ⟧Env ≡ ⟦ Op.⟦ x ⟧Var ρ ⟧Val
↦-sound (px • ρ) this = refl
↦-sound (px • ρ) (that x) = ↦-sound ρ x

eval-term-sound : ∀ {Γ τ} ρ v n (t : Term Γ τ) →
  eval-term t ρ n ≡ Done v →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

eval-fun-sound : ∀ {Γ τ} ρ v n (t : Fun Γ τ) →
  eval-fun t ρ n ≡ Done v →
  ⟦ t ⟧Fun ⟦ ρ ⟧Env ≡ ⟦ v ⟧Val

-- XXX Here we only need a degenerate form of this lemma, for variables.
apply-sound : ∀ {Γ σ τ} ρ v f a n (s : Term Γ (σ ⇒ τ)) t →
  ⟦ s ⟧Term ⟦ ρ ⟧Env ≡ ⟦ f ⟧Val →
  ⟦ t ⟧Term ⟦ ρ ⟧Env ≡ ⟦ a ⟧Val →
  apply f a n ≡ Done v →
  ⟦ s ⟧Term ⟦ ρ ⟧Env (⟦ t ⟧Term ⟦ ρ ⟧Env) ≡ ⟦ v ⟧Val
apply-sound _ v (closure ft ρ) a n s t feq aeq eq rewrite feq | aeq = eval-fun-sound (a • ρ) v n ft eq

eval-fun-sound ρ v n (term x) eq = eval-term-sound ρ v n x eq
eval-fun-sound ρ .(closure t ρ) n (abs t) refl = refl

eval-term-sound ρ v zero t ()
eval-term-sound ρ .(Op.⟦ x ⟧Var ρ) (ℕ.suc n) (var x) refl = ↦-sound ρ x
eval-term-sound ρ v (ℕ.suc n) (lett f x t) eq with apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n | inspect (apply (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ)) n
eval-term-sound ρ v (ℕ.suc n) (lett f x t) eq | Done fv | [ fveq ] rewrite apply-sound ρ fv (Op.⟦ f ⟧Var ρ) (Op.⟦ x ⟧Var ρ) n (var f) (var x) (↦-sound ρ f) (↦-sound ρ x) fveq = eval-term-sound (fv • ρ) v n t eq
eval-term-sound ρ v (ℕ.suc n) (lett f x t) () | Error | _
eval-term-sound ρ v (ℕ.suc n) (lett f x t) () | TimeOut | _
