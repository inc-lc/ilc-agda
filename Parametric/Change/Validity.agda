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
    ΔVal-base : Base → Set
    valid-base : ∀ {ι} → ⟦ ι ⟧Base → ΔVal-base ι → Set
    apply-ΔVal-base : ∀ ι → ⟦ ι ⟧Base → ΔVal-base ι → ⟦ ι ⟧Base
    diff-ΔVal-base : ∀ ι → ⟦ ι ⟧Base → ⟦ ι ⟧Base → ΔVal-base ι
    R[v,u-v]-base : ∀ {ι} {u v : ⟦ ι ⟧Base} → valid-base {ι} v (diff-ΔVal-base ι u v)
    v+[u-v]=u-base : ∀ {ι} {u v : ⟦ ι ⟧Base} → apply-ΔVal-base ι v (diff-ΔVal-base ι u v) ≡ u

  ---------------
  -- Interface --
  ---------------

  ΔVal : Type → Set
  valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set

  apply-ΔVal : ∀ τ → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
  diff-ΔVal : ∀ τ → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ

  infixl 6 apply-ΔVal diff-ΔVal -- as with + - in GHC.Num
  syntax apply-ΔVal τ v dv = v ⊞₍ τ ₎ dv
  syntax diff-ΔVal τ u v = u ⊟₍ τ ₎ v

  -- Lemma diff-is-valid
  R[v,u-v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊟₍ τ ₎ v)

  -- Lemma apply-diff
  v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
    v ⊞₍ τ ₎ (u ⊟₍ τ ₎ v) ≡ u

  --------------------
  -- Implementation --
  --------------------

  -- (ΔVal τ) is the set of changes of type τ. This set is
  -- strictly smaller than ⟦ ΔType τ⟧ if τ is a function type. In
  -- particular, (ΔVal (σ ⇒ τ)) is a function that accepts only
  -- valid changes, while ⟦ ΔType (σ ⇒ τ) ⟧ accepts also invalid
  -- changes.
  --
  -- ΔVal τ is the target of the denotational specification ⟦_⟧Δ.
  -- Detailed motivation:
  --
  -- https://github.com/ps-mr/ilc/blob/184a6291ac6eef80871c32d2483e3e62578baf06/POPL14/paper/sec-formal.tex
  -- ΔVal : Type → Set
  ΔVal (base ι) = ΔVal-base ι
  ΔVal (σ ⇒ τ) = (v : ⟦ σ ⟧) → (dv : ΔVal σ) → valid v dv → ΔVal τ

  -- _⊞_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
  n ⊞₍ base ι ₎ Δn = apply-ΔVal-base ι n Δn
  f ⊞₍ σ ⇒ τ ₎ Δf = λ v → f v ⊞₍ τ ₎ Δf v (v ⊟₍ σ ₎ v) (R[v,u-v] {σ})

  -- _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
  m ⊟₍ base ι ₎ n = diff-ΔVal-base ι m n
  g ⊟₍ σ ⇒ τ ₎ f = λ v Δv R[v,Δv] → g (v ⊞₍ σ ₎ Δv) ⊟₍ τ ₎ f v

  -- valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set
  valid {base ι} n Δn = valid-base {ι} n Δn
  valid {σ ⇒ τ} f Δf =
    ∀ (v : ⟦ σ ⟧) (Δv : ΔVal σ) (R[v,Δv] : valid v Δv)
    → valid {τ} (f v) (Δf v Δv R[v,Δv])
    -- × (f ⊞ Δf) (v ⊞ Δv) ≡ f v ⊞ Δf v Δv R[v,Δv]
    × (f ⊞₍ σ ⇒ τ ₎ Δf) (v ⊞₍ σ ₎ Δv) ≡ f v ⊞₍ τ ₎ Δf v Δv R[v,Δv]

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
  R[v,u-v] {σ ⇒ τ} {u} {v} = λ w Δw R[w,Δw] →
    let
      w′ = w ⊞₍ σ ₎ Δw
    in
      R[v,u-v] {τ}
      ,
      (begin
        (v ⊞₍ σ ⇒ τ ₎ (u ⊟₍ σ ⇒ τ ₎ v)) w′
      ≡⟨ cong (λ hole → hole w′) (v+[u-v]=u {σ ⇒ τ} {u} {v}) ⟩
        u w′
      ≡⟨ sym (v+[u-v]=u {τ} {u w′} {v w}) ⟩
        v w ⊞₍ τ ₎ (u ⊟₍ σ ⇒ τ ₎ v) w Δw R[w,Δw]
      ∎) where open ≡-Reasoning

  -- syntactic sugar for implicit indices
  infixl 6 _⊞_ _⊟_ -- as with + - in GHC.Num

  _⊞_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
  _⊞_ {τ} v dv = v ⊞₍ τ ₎ dv

  _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
  _⊟_ {τ} u v = u ⊟₍ τ ₎ v

  ------------------
  -- Environments --
  ------------------

  open DependentList public using (∅; _•_)
  open Tuples public using (cons)

  ΔEnv-Entry : Type → Set
  ΔEnv-Entry τ = Triple
    ⟦ τ ⟧
    (λ _ → ΔVal τ)
    (λ v dv → valid {τ} v dv)

  ΔEnv : Context → Set
  ΔEnv = DependentList ΔEnv-Entry

  ignore-entry : ΔEnv-Entry ⊆ ⟦_⟧
  ignore-entry (cons v _ _) = v

  update-entry : ΔEnv-Entry ⊆ ⟦_⟧
  update-entry {τ} (cons v dv R[v,dv]) = v ⊞₍ τ ₎ dv

  ignore : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
  ignore = map (λ {τ} → ignore-entry {τ})

  update : ∀ {Γ : Context} → (ρ : ΔEnv Γ) → ⟦ Γ ⟧
  update = map (λ {τ} → update-entry {τ})
