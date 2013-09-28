module Denotation.Change.Popl14 where

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
open import Popl14.Denotation.Value
open import Theorem.Groups-Popl14
open import Postulate.Extensionality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Popl14

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
ΔVal (base base-int) = ℤ
ΔVal (base base-bag) = Bag
ΔVal (σ ⇒ τ) = (v : ⟦ σ ⟧) → (dv : ΔVal σ) → valid v dv → ΔVal τ

-- _⊞_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
n ⊞₍ base base-int ₎ Δn = n + Δn
b ⊞₍ base base-bag ₎ Δb = b ++ Δb
f ⊞₍ σ ⇒ τ ₎ Δf = λ v → f v ⊞₍ τ ₎ Δf v (v ⊟₍ σ ₎ v) (R[v,u-v] {σ})

-- _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
m ⊟₍ base base-int ₎ n = m - n
d ⊟₍ base base-bag ₎ b = d \\ b
g ⊟₍ σ ⇒ τ ₎ f = λ v Δv R[v,Δv] → g (v ⊞₍ σ ₎ Δv) ⊟₍ τ ₎ f v

-- valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set
valid {base base-int} n Δn = ⊤
valid {base base-bag} b Δb = ⊤
valid {σ ⇒ τ} f Δf =
  ∀ (v : ⟦ σ ⟧) (Δv : ΔVal σ) (R[v,Δv] : valid v Δv)
  → valid (f v) (Δf v Δv R[v,Δv])
  -- × (f ⊞ Δf) (v ⊞ Δv) ≡ f v ⊞ Δf v Δv R[v,Δv]
  × (f ⊞₍ σ ⇒ τ ₎ Δf) (v ⊞₍ σ ₎ Δv) ≡ f v ⊞₍ τ ₎ Δf v Δv R[v,Δv]

-- v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊞ (u ⊟ v) ≡ u
v+[u-v]=u {base base-int} {u} {v} = n+[m-n]=m {v} {u}
v+[u-v]=u {base base-bag} {u} {v} = a++[b\\a]=b {v} {u}
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

R[v,u-v] {base base-int} {u} {v} = tt
R[v,u-v] {base base-bag} {u} {v} = tt
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

-- `diff` and `apply`, without validity proofs
infixl 6 _⟦⊕⟧_ _⟦⊝⟧_
_⟦⊕⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
_⟦⊝⟧_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧

_⟦⊕⟧_ {base base-int}  n Δn = n +  Δn
_⟦⊕⟧_ {base base-bag}  b Δb = b ++ Δb
_⟦⊕⟧_ {σ ⇒ τ} f Δf = λ v →
  let
    _-₀_ = _⟦⊝⟧_ {σ}
    _+₁_ = _⟦⊕⟧_ {τ}
  in
    f v +₁ Δf v (v -₀ v)

_⟦⊝⟧_ {base base-int}  m n = m -  n
_⟦⊝⟧_ {base base-bag}  a b = a \\ b
_⟦⊝⟧_ {σ ⇒ τ} g f = λ v Δv → _⟦⊝⟧_ {τ} (g (_⟦⊕⟧_ {σ} v Δv)) (f v)
