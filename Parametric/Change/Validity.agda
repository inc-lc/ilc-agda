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
    Change-base : Base → Set
    valid-base : ∀ {ι} → ⟦ ι ⟧Base → Change-base ι → Set
    apply-change-base : ∀ ι → ⟦ ι ⟧Base → Change-base ι → ⟦ ι ⟧Base
    diff-change-base : ∀ ι → ⟦ ι ⟧Base → ⟦ ι ⟧Base → Change-base ι
    R[v,u-v]-base : ∀ {ι} {u v : ⟦ ι ⟧Base} → valid-base {ι} v (diff-change-base ι u v)
    v+[u-v]=u-base : ∀ {ι} {u v : ⟦ ι ⟧Base} → apply-change-base ι v (diff-change-base ι u v) ≡ u

  ---------------
  -- Interface --
  ---------------

  Change : Type → Set
  valid : ∀ {τ} → ⟦ τ ⟧ → Change τ → Set

  apply-change : ∀ τ → ⟦ τ ⟧ → Change τ → ⟦ τ ⟧
  diff-change : ∀ τ → ⟦ τ ⟧ → ⟦ τ ⟧ → Change τ

  infixl 6 apply-change diff-change -- as with + - in GHC.Num
  syntax apply-change τ v dv = v ⊞₍ τ ₎ dv
  syntax diff-change τ u v = u ⊟₍ τ ₎ v

  -- Lemma diff-is-valid
  R[v,u-v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊟₍ τ ₎ v)

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
  ValidChange : Type → Set
  ValidChange τ = Triple
    ⟦ τ ⟧
    (λ _ → Change τ)
    (λ v dv → valid {τ} v dv)

  -- Change : Type → Set
  Change (base ι) = Change-base ι
  Change (σ ⇒ τ) = ValidChange σ → Change τ

  before : ValidChange ⊆ ⟦_⟧
  before (cons v _ _) = v

  after : ValidChange ⊆ ⟦_⟧
  after {τ} (cons v dv R[v,dv]) = v ⊞₍ τ ₎ dv

  diff-valid-change : ∀ τ → (u v : ⟦ τ ⟧) → ValidChange τ
  diff-valid-change τ u v = cons v (u ⊟₍ τ ₎ v) (R[v,u-v] {τ} {u} {v})

  nil-valid-change : ∀ τ → ⟦ τ ⟧ → ValidChange τ
  nil-valid-change τ v = diff-valid-change τ v v

  -- _⊞_ : ∀ {τ} → ⟦ τ ⟧ → Change τ → ⟦ τ ⟧
  n ⊞₍ base ι ₎ Δn = apply-change-base ι n Δn
  f ⊞₍ σ ⇒ τ ₎ Δf = λ v → f v ⊞₍ τ ₎ Δf (nil-valid-change σ v)

  -- _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → Change τ
  m ⊟₍ base ι ₎ n = diff-change-base ι m n
  g ⊟₍ σ ⇒ τ ₎ f = λ v → g (after v) ⊟₍ τ ₎ f (before v)

  -- valid : ∀ {τ} → ⟦ τ ⟧ → Change τ → Set
  valid {base ι} n Δn = valid-base {ι} n Δn
  valid {σ ⇒ τ} f Δf =
    ∀ (v : ValidChange σ)
    → valid {τ} (f (before v)) (Δf v)
    -- × (f ⊞ Δf) (v ⊞ Δv) ≡ f v ⊞ Δf v Δv R[v,Δv]
    × (f ⊞₍ σ ⇒ τ ₎ Δf) (after v) ≡ f (before v) ⊞₍ τ ₎ Δf v

  -- v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊞ (u ⊟ v) ≡ u
  v+[u-v]=u {base ι} {u} {v} = v+[u-v]=u-base {ι} {u} {v}
  v+[u-v]=u {σ ⇒ τ} {u} {v} =
      ext {-⟦ σ ⟧} {λ _ → ⟦ τ ⟧-} (λ w →
        begin
          (v ⊞₍ σ ⇒ τ ₎ (u ⊟₍ σ ⇒ τ ₎ v)) w
        ≡⟨ refl ⟩
          v w ⊞₍ τ ₎ (u (w ⊞₍ σ ₎ (w ⊟₍ σ ₎ w)) ⊟₍ τ ₎ v w)
        ≡⟨ cong (λ hole → v w ⊞₍ τ ₎ (u hole ⊟₍ τ ₎ v w)) (v+[u-v]=u {σ}) ⟩
          v w ⊞₍ τ ₎ (u w ⊟₍ τ ₎ v w)
        ≡⟨ v+[u-v]=u {τ} ⟩
          u w
        ∎) where
        open ≡-Reasoning

  R[v,u-v] {base ι} {u} {v} = R[v,u-v]-base {ι} {u} {v}
  R[v,u-v] {σ ⇒ τ} {u} {v} = λ w →
    let
      w′ = after {σ} w
    in
      R[v,u-v] {τ}
      ,
      (begin
        (v ⊞₍ σ ⇒ τ ₎ (u ⊟₍ σ ⇒ τ ₎ v)) w′
      ≡⟨ cong (λ hole → hole w′) (v+[u-v]=u {σ ⇒ τ} {u} {v}) ⟩
        u w′
      ≡⟨ sym (v+[u-v]=u {τ} {u w′} {v (before {σ} w)}) ⟩
        v (before {σ} w) ⊞₍ τ ₎ (u ⊟₍ σ ⇒ τ ₎ v) w
      ∎) where open ≡-Reasoning

  -- syntactic sugar for implicit indices
  infixl 6 _⊞_ _⊟_ -- as with + - in GHC.Num

  _⊞_ : ∀ {τ} → ⟦ τ ⟧ → Change τ → ⟦ τ ⟧
  _⊞_ {τ} v dv = v ⊞₍ τ ₎ dv

  _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → Change τ
  _⊟_ {τ} u v = u ⊟₍ τ ₎ v

  ------------------
  -- Environments --
  ------------------

  open DependentList public using (∅; _•_)
  open Tuples public using (cons)

  ΔEnv : Context → Set
  ΔEnv = DependentList ValidChange

  ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
  ignore = map (λ {τ} → before {τ})

  update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
  update = map (λ {τ} → after {τ})
