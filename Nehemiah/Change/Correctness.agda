------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Correctness of differentiation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Correctness where

-- The denotational properties of the `derive` transformation
-- for Calculus Nehemiah. In particular, the main theorem
-- about it producing the correct incremental behavior.

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term
open import Nehemiah.Change.Value
open import Nehemiah.Change.Evaluation
open import Nehemiah.Change.Validity
open import Nehemiah.Change.Derive
open import Nehemiah.Change.Implementation

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Theorem.Groups-Nehemiah
open import Postulate.Extensionality

import Parametric.Change.Correctness
  Const ⟦_⟧Base ⟦_⟧Const ΔBase
  apply-base diff-base nil-base
  ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
  meaning-⊕-base meaning-⊝-base meaning-onil-base
  deriveConst implementation-structure as Correctness

open import Algebra.Structures

private
  open import Level using () renaming (zero to lzero)
  open FunctionChanges {c = lzero} {d = lzero} ℤ Bag using (FunctionChange; changeAlgebra)

  flatmap-funarg-equal : ∀ (f : ℤ → Bag) (Δf : Δ f) Δf′ (Δf≈Δf′ : Δf ≈₍ int ⇒ bag ₎ Δf′) →
    (f ⊞ Δf) ≡ (f ⟦⊕₍ int ⇒ bag ₎⟧ Δf′)
  flatmap-funarg-equal f Δf Δf′ Δf≈Δf′ = ext lemma
    where
    lemma : ∀ v → f v ++ FunctionChange.apply Δf v (+ 0) ≡ f v ++ Δf′ v (+ 0)
    lemma v rewrite Δf≈Δf′ v (+ 0) (+ 0) refl = refl

derive-const-correct : Correctness.Structure
derive-const-correct (intlit-const n) = refl
derive-const-correct add-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl
  rewrite mn·pq=mp·nq {w} {Δw} {w₁} {Δw₁}
  | associative-int (w + w₁) (Δw + Δw₁) (- (w + w₁))
  = n+[m-n]=m {w + w₁} {Δw + Δw₁}
derive-const-correct minus-const w Δw .Δw refl
  rewrite sym (-m·-n=-mn {w} {Δw})
  | associative-int (- w) (- Δw) (- (- w)) = n+[m-n]=m { - w} { - Δw}
derive-const-correct empty-const = refl
derive-const-correct insert-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl = refl
derive-const-correct union-const w Δw .Δw refl w₁ Δw₁ .Δw₁ refl
  rewrite ab·cd=ac·bd {w} {Δw} {w₁} {Δw₁}
  | associative-bag (w ++ w₁) (Δw ++ Δw₁) (negateBag (w ++ w₁))
  = a++[b\\a]=b {w ++ w₁} {Δw ++ Δw₁}
derive-const-correct negate-const w Δw .Δw refl
  rewrite sym (-a·-b=-ab {w} {Δw})
  | associative-bag (negateBag w) (negateBag Δw) (negateBag (negateBag w))
  = a++[b\\a]=b {negateBag w} {negateBag Δw}
derive-const-correct flatmap-const w Δw Δw′ Δw≈Δw′ w₁ Δw₁ .Δw₁ refl
  rewrite flatmap-funarg-equal w Δw Δw′ Δw≈Δw′ = refl
derive-const-correct sum-const w Δw .Δw refl
  rewrite homo-sum {w} {Δw}
  | associative-int (sumBag w) (sumBag Δw) (- sumBag w)
  = n+[m-n]=m {sumBag w} {sumBag Δw}

open Correctness.Structure derive-const-correct public
