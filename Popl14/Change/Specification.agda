module Popl14.Change.Specification where

-- Denotation-as-specification for Calculus Popl14
--
-- Contents
-- - ⟦_⟧Δ : binding-time-shifted derive
-- - Validity and correctness lemmas for ⟦_⟧Δ
-- - `corollary`: ⟦_⟧Δ reacts to both environment and arguments
-- - `corollary-closed`: binding-time-shifted main theorem

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
open import Popl14.Denotation.Evaluation
open import Popl14.Change.Validity

open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Theorem.Groups-Popl14

import Parametric.Change.Specification
  Const ⟦_⟧Base ⟦_⟧Const change-algebra-base-family as Specification

private
  ⟦_⟧ΔConst : ∀ {Σ τ} → (c  : Const Σ τ) (ρ : ⟦ Σ ⟧) → Δ₍ Σ ₎ ρ → Δ₍ τ ₎ (⟦ c ⟧Const ρ)
  ⟦ intlit-const n ⟧ΔConst ∅ ∅ = + 0
  ⟦ add-const ⟧ΔConst (n₁ • n₂ • ∅) (dn₁ • dn₂ • ∅) = dn₁ + dn₂
  ⟦ minus-const ⟧ΔConst (n • ∅) (dn • ∅) = - dn
  ⟦ empty-const ⟧ΔConst ∅ ∅ = emptyBag
  ⟦ insert-const ⟧ΔConst (n • b • ∅) (dn • db • ∅) =
      (singletonBag (n + dn) ++ (b ++ db)) \\ (singletonBag n ++ b)
  ⟦ union-const ⟧ΔConst (b₁ • b₂ • ∅) (db₁ • db₂ • ∅) = db₁ ++ db₂
  ⟦ negate-const ⟧ΔConst (b • ∅) (db • ∅) = negateBag db
  ⟦ flatmap-const ⟧ΔConst (f • b • ∅) (df • db • ∅) =
      flatmapBag (f ⊞₍ int ⇒ bag ₎ df) (b ++ db) \\ flatmapBag f b
  ⟦ sum-const ⟧ΔConst (b • ∅) (db • ∅) = sumBag db

  correctness-const : ∀ {Σ τ} (c : Const Σ τ) →
    Derivative₍ Σ , τ ₎ ⟦ c ⟧Const ⟦ c ⟧ΔConst
  correctness-const (intlit-const n) ∅ ∅ = right-id-int n
  correctness-const add-const (n₁ • n₂ • ∅) (dn₁ • dn₂ • ∅) =
    mn·pq=mp·nq {n₁} {n₂} {dn₁} {dn₂}
  correctness-const minus-const (n • ∅) (dn • ∅) = -m·-n=-mn {n} {dn}
  correctness-const empty-const ∅ ∅ = right-id-bag emptyBag
  correctness-const insert-const (n • b • ∅) (dn • db • ∅) = a++[b\\a]=b
  correctness-const union-const (b₁ • b₂ • ∅) (db₁ • db₂ • ∅) = ab·cd=ac·bd
  correctness-const negate-const (b • ∅) (db • ∅) = -a·-b=-ab
  correctness-const flatmap-const (f • b • ∅) (df • db • ∅) = a++[b\\a]=b
  correctness-const sum-const (b • ∅) (db • ∅) = sym homo-sum

specification-structure : Specification.Structure
specification-structure = record
    { ⟦_⟧ΔConst = ⟦_⟧ΔConst
    ; correctness-const = correctness-const
    }

open Specification.Structure specification-structure public
