module Thesis.Subst where

--------------------------------------------------------------------------------
-- Prove substitution lemma. Unfortunately, this is done using a quite different
-- machinery from what we use elsewhere. The machinery for defining substitution
-- is taken from a formalization of hereditary substitution (Hereditary
-- Substitutions for Simple Types, Formalized, by Keller and Altenkirch), and
-- uses a different machinery for weakening.

-- I developed the lemmas relating substitution and this form of weakening from
-- scratch.
--------------------------------------------------------------------------------

open import Thesis.Lang hiding (_-_)

_-_ : ∀ {σ} Γ → Var Γ σ → Context
∅ - ()
(σ • Γ) - this = Γ
(τ • Γ) - that x = τ • (Γ - x)

import Relation.Binary.PropositionalEquality as P
open P hiding (subst)
open import Postulate.Extensionality

extend-env : ∀ {σ Γ} (x : Var Γ σ) (rho : ⟦ Γ - x ⟧Context) (v : ⟦ σ ⟧Type) → ⟦ Γ ⟧Context
extend-env this rho v = v • rho
extend-env (that x) (v1 • rho) v = v1 • extend-env x rho v

extend-env-sound : ∀ {σ Γ} (x : Var Γ σ) (rho : ⟦ Γ - x ⟧Context) (v : ⟦ σ ⟧Type) → v ≡ ⟦ x ⟧Var (extend-env x rho v)
extend-env-sound this rho v = refl
extend-env-sound (that x) (v1 • rho) v = extend-env-sound x rho v

wkv : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv this y = that y
wkv (that x) this = this
wkv (that x) (that y) = that (wkv x y)

data EqV : ∀ {Γ σ τ} → Var Γ σ → Var Γ τ → Set where
  same : ∀ {Γ σ} → {x : Var Γ σ} → EqV x x
  diff : ∀ {Γ σ τ} → (x : Var Γ σ) → (z : Var (Γ - x) τ) → EqV x (wkv x z)
  -- If x and y do not represent the same variable, then
  -- ∃ z. y ≡ wkv x z, allowing us to construct a proof that diff x z : EqV x y

eq : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq this this = same
eq this (that y) = diff this y
eq (that x) this = diff (that x) this
eq (that x) (that y) with eq x y
eq (that y) (that .y) | same = same
eq (that x) (that .(wkv x z)) | diff .x z = diff (that x) (that z)

wkTerm : ∀ {Γ σ τ} → (x : Var Γ σ) → Term (Γ - x) τ → Term Γ τ
wkTerm x (var v) = var (wkv x v)
wkTerm x (app t₁ t₂) = (app (wkTerm x t₁) (wkTerm x t₂))
wkTerm x (abs t) = abs (wkTerm (that x) t)
wkTerm x (const c) = const c

wkv-sound : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) →
  (ρ : ⟦ Γ - x ⟧Context) (v : ⟦ σ ⟧Type) →
  ⟦ wkv x y ⟧Var (extend-env x ρ v) ≡ ⟦ y ⟧Var ρ
wkv-sound this y ρ v = refl
wkv-sound (that x) this (v0 • ρ) v = refl
wkv-sound (that x) (that y) (v0 • ρ) v = wkv-sound x y ρ v

wkTerm-sound : ∀ {Γ σ τ} → (x : Var Γ σ) → (t : Term (Γ - x) τ) →
  (ρ : ⟦ Γ - x ⟧Context) (v : ⟦ σ ⟧Type) →
  ⟦ wkTerm x t ⟧Term (extend-env x ρ v) ≡ ⟦ t ⟧Term ρ
wkTerm-sound x (const c) ρ v = refl
wkTerm-sound x (var y) ρ v = wkv-sound x y ρ v
wkTerm-sound x (app t₁ t₂) ρ v
  rewrite wkTerm-sound x t₁ ρ v
  | wkTerm-sound x t₂ ρ v = refl
wkTerm-sound x (abs t) ρ v = ext (λ v₁ → wkTerm-sound (that x) t (v₁ • ρ) v)

substVar : ∀ {Γ σ τ} → Var Γ τ → (x : Var Γ σ) → Term (Γ - x) σ → Term (Γ - x) τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv x z) x u | diff .x z = var z

-- The above is the crucial rule. The dotted pattern makes producing the result
-- easy.

subst : ∀ {Γ σ τ} → Term Γ τ → (x : Var Γ σ) → Term (Γ - x) σ → Term (Γ - x) τ
subst (var v) x u = substVar v x u
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)
subst (abs t) x u = abs (subst t (that x) (wkTerm this u))
subst (const c) x u = const c

substVar-lemma : ∀ {σ τ Γ} (v : Var Γ τ) (x : Var Γ σ) s rho → ⟦ substVar v x s ⟧Term rho ≡ ⟦ v ⟧Var (extend-env x rho (⟦ s ⟧Term rho))
substVar-lemma v x s rho with eq x v
substVar-lemma .(wkv x z) x s rho | diff .x z = sym (wkv-sound x z rho (⟦ s ⟧Term rho))
substVar-lemma x .x s rho | same = extend-env-sound x rho (⟦ s ⟧Term rho)

subst-lemma : ∀ {σ τ Γ} (t : Term Γ τ) (x : Var Γ σ) s rho → ⟦ subst t x s ⟧Term rho ≡ ⟦ t ⟧Term (extend-env x rho (⟦ s ⟧Term rho))
subst-lemma (const c) x s rho = refl
subst-lemma (var y) x s rho = substVar-lemma y x s rho
subst-lemma (app t₁ t₂) x s rho rewrite subst-lemma t₁ x s rho | subst-lemma t₂ x s rho = refl
subst-lemma (abs t) x s rho = ext body
  where
    body : ∀ v → ⟦ subst t (that x) (wkTerm this s) ⟧Term (v • rho) ≡
           ⟦ t ⟧Term (v • extend-env x rho (⟦ s ⟧Term rho))
    body v rewrite subst-lemma t (that x) (wkTerm this s) (v • rho) |
      wkTerm-sound this s rho v = refl
