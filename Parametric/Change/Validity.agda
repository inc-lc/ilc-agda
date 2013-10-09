import Parametric.Syntax.Type as Type
import Parametric.Denotation.Value as Value

module Parametric.Change.Validity
    {Base : Type.Structure}
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Value.Structure Base ⟦_⟧Base

-- Changes for Calculus Popl14
--
-- Contents
-- - Mutually recursive concepts: ΔVal, validity.
--     Under module Syntax, the corresponding concepts of
--     ΔType and ΔContext reside in separate files.
--     Now they have to be together due to mutual recursiveness.
-- - `diff` and `apply` on semantic values of changes:
--     they have to be here as well because they are mutually
--     recursive with validity.
-- - The lemma diff-is-valid: it has to be here because it is
--     mutually recursive with `apply`
-- - The lemma apply-diff: it is mutually recursive with `apply`
--     and `diff`

open import Base.Denotation.Notation public

open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality
open import Data.Product hiding (map)

import Structure.Tuples as Tuples
open Tuples

import Base.Data.DependentList as DependentList
open DependentList

open import Relation.Unary using (_⊆_)

record Structure : Set₁ where
  ----------------
  -- Parameters --
  ----------------

  field
    Change-base : (ι : Base) → ⟦ ι ⟧Base → Set
    apply-change-base : ∀ ι → (v : ⟦ ι ⟧Base) → Change-base ι v → ⟦ ι ⟧Base
    diff-change-base : ∀ ι → (u v : ⟦ ι ⟧Base) → Change-base ι v
    v+[u-v]=u-base : ∀ {ι} {u v : ⟦ ι ⟧Base} → apply-change-base ι v (diff-change-base ι u v) ≡ u

  ---------------
  -- Interface --
  ---------------

  Change : (τ : Type) → ⟦ τ ⟧ → Set

  apply-change : ∀ τ → (v : ⟦ τ ⟧) (dv : Change τ v) → ⟦ τ ⟧
  diff-change : ∀ τ → (u v : ⟦ τ ⟧) → Change τ v

  infixl 6 apply-change diff-change -- as with + - in GHC.Num
  syntax apply-change τ v dv = v ⊞₍ τ ₎ dv
  syntax diff-change τ u v = u ⊟₍ τ ₎ v

  -- Lemma apply-diff
  v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
    v ⊞₍ τ ₎ (u ⊟₍ τ ₎ v) ≡ u

  --------------------
  -- Implementation --
  --------------------

  -- (Change τ) is the set of changes of type τ. This set is
  -- strictly smaller than ⟦ ΔType τ⟧ if τ is a function type. In
  -- particular, (Change (σ ⇒ τ)) is a function that accepts only
  -- valid changes, while ⟦ ΔType (σ ⇒ τ) ⟧ accepts also invalid
  -- changes.
  --
  -- Change τ is the target of the denotational specification ⟦_⟧Δ.
  -- Detailed motivation:
  --
  -- https://github.com/ps-mr/ilc/blob/184a6291ac6eef80871c32d2483e3e62578baf06/POPL14/paper/sec-formal.tex


  nil-change : ∀ τ v → Change τ v

  -- Change : Type → Set
  Change (base ι) v = Change-base ι v
  Change (σ ⇒ τ) f = Pair
    (∀ v → Change σ v → Change τ (f v))
    (λ Δf → ∀ v dv →
      f (v ⊞₍ σ ₎ dv) ⊞₍ τ ₎ Δf (v ⊞₍ σ ₎ dv) (nil-change σ (v ⊞₍ σ ₎ dv)) ≡ f v ⊞₍ τ ₎ Δf v dv)

  before : ∀ {τ v} → Change τ v → ⟦ τ ⟧
  before {τ} {v} _ = v

  after : ∀ {τ v} → Change τ v → ⟦ τ ⟧
  after {τ} {v} dv = v ⊞₍ τ ₎ dv

  open Pair public using () renaming
    ( cdr to is-valid
    ; car to call-change
    )

  nil-change τ v = diff-change τ v v

  -- _⊞_ : ∀ {τ} → ⟦ τ ⟧ → Change τ → ⟦ τ ⟧
  apply-change (base ι) n Δn = apply-change-base ι n Δn
  apply-change (σ ⇒ τ) f Δf = λ v → f v ⊞₍ τ ₎ call-change Δf v (nil-change σ v)

  -- _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → Change τ
  diff-change (base ι) m n = diff-change-base ι m n
  diff-change (σ ⇒ τ) g f = cons (λ v dv → g (after {σ} dv) ⊟₍ τ ₎ f v)
    (λ v dv →
      begin
        f (v ⊞₍ σ ₎ dv) ⊞₍ τ ₎ (g ((v ⊞₍ σ ₎ dv) ⊞₍ σ ₎ ((v ⊞₍ σ ₎ dv) ⊟₍ σ ₎ (v ⊞₍ σ ₎ dv))) ⊟₍ τ ₎ f (v ⊞₍ σ ₎ dv))
      ≡⟨ cong (λ □ → f (v ⊞₍ σ ₎ dv) ⊞₍ τ ₎ (g □ ⊟₍ τ ₎ (f (v ⊞₍ σ ₎ dv))))
              (v+[u-v]=u {σ} {v ⊞₍ σ ₎ dv} {v ⊞₍ σ ₎ dv}) ⟩
        f (v ⊞₍ σ ₎ dv) ⊞₍ τ ₎ (g (v ⊞₍ σ ₎ dv) ⊟₍ τ ₎ f (v ⊞₍ σ ₎ dv))
      ≡⟨ v+[u-v]=u {τ} {g (v ⊞₍ σ ₎ dv)} {f (v ⊞₍ σ ₎ dv)} ⟩
        g (v ⊞₍ σ ₎ dv)
      ≡⟨  sym (v+[u-v]=u {τ} {g (v ⊞₍ σ ₎ dv)} {f v} )  ⟩
        f v ⊞₍ τ ₎ (g (v ⊞₍ σ ₎ dv) ⊟₍ τ ₎ f v)
      ∎) where open ≡-Reasoning

  -- call this lemma "replace"?
  -- v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊞ (u ⊟ v) ≡ u
  v+[u-v]=u {base ι} {u} {v} = v+[u-v]=u-base {ι} {u} {v}
  v+[u-v]=u {σ ⇒ τ} {u} {v} =
      ext {-⟦ σ ⟧} {λ _ → ⟦ τ ⟧-} (λ w →
        begin
          (apply-change (σ ⇒ τ) v (diff-change (σ ⇒ τ) u v)) w
        ≡⟨ refl ⟩
          v w ⊞₍ τ ₎ (u (w ⊞₍ σ ₎ (w ⊟₍ σ ₎ w)) ⊟₍ τ ₎ v w)
        ≡⟨ cong (λ hole → v w ⊞₍ τ ₎ (u hole ⊟₍ τ ₎ v w)) (v+[u-v]=u {σ}) ⟩
          v w ⊞₍ τ ₎ (u w ⊟₍ τ ₎ v w)
        ≡⟨ v+[u-v]=u {τ} ⟩
          u w
        ∎) where
        open ≡-Reasoning

  -- syntactic sugar for implicit indices
  infixl 6 _⊞_ _⊟_ -- as with + - in GHC.Num

  _⊞_ : ∀ {τ} → (v : ⟦ τ ⟧) → Change τ v → ⟦ τ ⟧
  _⊞_ {τ} v dv = v ⊞₍ τ ₎ dv

  _⊟_ : ∀ {τ} → (u v : ⟦ τ ⟧) → Change τ v
  _⊟_ {τ} u v = u ⊟₍ τ ₎ v

  ------------------
  -- Environments --
  ------------------

  open DependentList public using (∅; _•_)
  open Tuples public using (cons)

  data ΔEnv : ∀ (Γ : Context) → ⟦ Γ ⟧ → Set where
    ∅ : ΔEnv ∅ ∅
    _•_ : ∀ {τ Γ v ρ} →
      (dv : Change τ v) →
      (dρ : ΔEnv Γ ρ) →
      ΔEnv (τ • Γ) (v • ρ)

  ignore : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : ΔEnv Γ ρ) → ⟦ Γ ⟧
  ignore {Γ} {ρ} _ = ρ

  update : ∀ {Γ : Context} → {ρ : ⟦ Γ ⟧} (dρ : ΔEnv Γ ρ) → ⟦ Γ ⟧
  update ∅ = ∅
  update {τ • Γ} (dv • dρ) = after {τ} dv • update dρ
