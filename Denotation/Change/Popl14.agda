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

infixl 6 _⊞_ _⊟_ -- as with + - in GHC.Num
-- apply Δv v ::= v ⊞ Δv
_⊞_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
--   diff u v ::= u ⊟ v
_⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ

-- Lemma diff-is-valid
R[v,u-v] : ∀ {τ : Type} {u v : ⟦ τ ⟧} → valid {τ} v (u ⊟ v)

-- Lemma apply-diff
v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
  let
    _+_ = _⊞_ {τ}
    _-_ = _⊟_ {τ}
  in
  v + (u - v) ≡ u

--------------------
-- Implementation --
--------------------

-- ΔVal τ is intended to be the semantic domain for changes of values
-- of type τ.
--
-- ΔVal τ is the target of the denotational specification ⟦_⟧Δ.
-- Detailed motivation:
--
-- https://github.com/ps-mr/ilc/blob/184a6291ac6eef80871c32d2483e3e62578baf06/POPL14/paper/sec-formal.tex
--
-- ΔVal : Type → Set
ΔVal (base base-int) = ℤ
ΔVal (base base-bag) = Bag
ΔVal (σ ⇒ τ) = (v : ⟦ σ ⟧) → (dv : ΔVal σ) → valid v dv → ΔVal τ

-- _⊞_ : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → ⟦ τ ⟧
_⊞_ {base base-int} n Δn = n + Δn
_⊞_ {base base-bag} b Δb = b ++ Δb
_⊞_ {σ ⇒ τ} f Δf = λ v → f v ⊞ Δf v (v ⊟ v) (R[v,u-v] {σ})

-- _⊟_ : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ΔVal τ
_⊟_ {base base-int} m n = m - n
_⊟_ {base base-bag} d b = d \\ b
_⊟_ {σ ⇒ τ} g f = λ v Δv R[v,Δv] → g (v ⊞ Δv) ⊟ f v

-- valid : ∀ {τ} → ⟦ τ ⟧ → ΔVal τ → Set
valid {base base-int} n Δn = ⊤
valid {base base-bag} b Δb = ⊤
valid {σ ⇒ τ} f Δf =
  ∀ (v : ⟦ σ ⟧) (Δv : ΔVal σ) (R[v,Δv] : valid v Δv)
  → valid (f v) (Δf v Δv R[v,Δv])
  -- × (f ⊞ Δf) (v ⊞ Δv) ≡ f v ⊞ Δf v Δv R[v,Δv]
  × (_⊞_ {σ ⇒ τ} f Δf) (v ⊞ Δv) ≡ f v ⊞ Δf v Δv R[v,Δv]

-- v+[u-v]=u : ∀ {τ : Type} {u v : ⟦ τ ⟧} → v ⊞ (u ⊟ v) ≡ u
v+[u-v]=u {base base-int} {u} {v} = n+[m-n]=m {v} {u}
v+[u-v]=u {base base-bag} {u} {v} = a++[b\\a]=b {v} {u}
v+[u-v]=u {σ ⇒ τ} {u} {v} =
  let
    _+_ = _⊞_ {σ ⇒ τ}
    _-_ = _⊟_ {σ ⇒ τ}
    _+₀_ = _⊞_ {σ}
    _-₀_ = _⊟_ {σ}
    _+₁_ = _⊞_ {τ}
    _-₁_ = _⊟_ {τ}
  in
    ext {-⟦ σ ⟧} {λ _ → ⟦ τ ⟧-} (λ w →
      begin
        (v + (u - v)) w
      ≡⟨ refl ⟩
        v w +₁ (u (w +₀ (w -₀ w)) -₁ v w)
      ≡⟨ cong (λ hole → v w +₁ (u hole -₁ v w)) (v+[u-v]=u {σ}) ⟩
        v w +₁ (u w -₁ v w)
      ≡⟨ v+[u-v]=u {τ} ⟩
        u w
      ∎) where
      open ≡-Reasoning

R[v,u-v] {base base-int} {u} {v} = tt
R[v,u-v] {base base-bag} {u} {v} = tt
R[v,u-v] {σ ⇒ τ} {u} {v} = λ w Δw R[w,Δw] →
  let
    w′ = w ⊞ Δw
    _+_ = _⊞_ {σ ⇒ τ}
    _-_ = _⊟_ {σ ⇒ τ}
    _+₁_ = _⊞_ {τ}
    _-₁_ = _⊟_ {τ}
  in
    R[v,u-v] {τ}
    ,
    (begin
      (v + (u - v)) w′
    ≡⟨ cong (λ hole → hole w′) (v+[u-v]=u {σ ⇒ τ} {u} {v}) ⟩
      u w′
    ≡⟨ sym (v+[u-v]=u {τ} {u w′} {v w}) ⟩
      v w +₁ (u - v) w Δw R[w,Δw]
    ∎) where open ≡-Reasoning

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
