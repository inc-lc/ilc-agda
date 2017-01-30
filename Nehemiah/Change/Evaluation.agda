------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Connecting Nehemiah.Change.Term and Nehemiah.Change.Value.
------------------------------------------------------------------------

module Nehemiah.Change.Evaluation where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term
open import Nehemiah.Change.Value
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation

import Parametric.Change.Evaluation
    ⟦_⟧Base ⟦_⟧Const ΔBase apply-base diff-base nil-base ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧
  as ChangeEvaluation

private
  {-# TERMINATING #-}
  meaning-⊕-base : ChangeEvaluation.ApplyStructure
  meaning-⊝-base : ChangeEvaluation.DiffStructure
  meaning-onil-base : ChangeEvaluation.NilStructure
  meaning-⊕-invariant-base : ChangeEvaluation.ApplyInvariantStructure
  meaning-⊝-invariant-base : ChangeEvaluation.DiffInvariantStructure
  meaning-onil-invariant-base : ChangeEvaluation.NilInvariantStructure

meaning-structure : ChangeEvaluation.Structure
meaning-structure = record
  { meaning-⊕-base = meaning-⊕-base
  ; meaning-⊝-base = meaning-⊝-base
  ; meaning-onil-base = meaning-onil-base
  ; meaning-⊕-invariant-base = meaning-⊕-invariant-base
  ; meaning-⊝-invariant-base = meaning-⊝-invariant-base
  ; meaning-onil-invariant-base = meaning-onil-invariant-base
  }

module R = ChangeEvaluation.Structure meaning-structure
open import Postulate.Extensionality
meaning-⊕-invariant-base base-int Γ₁≼Γ₂ ρ = refl
meaning-⊕-invariant-base base-bag Γ₁≼Γ₂ ρ = refl
meaning-⊕-invariant-base (base-pair τ₁ τ₂) {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ = ext (λ dp → ext (goal dp))
  where
    module _ (dp : ⟦ _pair_ (ΔType τ₁) (ΔType τ₂) ⟧) (p : ⟦ _pair_ τ₁ τ₂ ⟧) where
      Γ₁′ Γ₂′ : Context
      Γ₁′ = (_pair_ τ₁ τ₂) • (_pair_ (ΔType τ₁) (ΔType τ₂)) • Γ₁
      Γ₂′ = (_pair_ τ₁ τ₂) • (_pair_ (ΔType τ₁) (ΔType τ₂)) • Γ₂
      ρ₂′ : ⟦ Γ₂′ ⟧Context
      ρ₂′ = p • dp • ρ
      Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
      Γ₁′≼Γ₂′ = keep _ • keep _ • Γ₁≼Γ₂
      ρ₁′ : ⟦ Γ₁′ ⟧Context
      ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
      explain : ρ₁′ ≡ p • dp • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
      explain = refl
      goal :
        (⟦ apply-term {τ₁} ⟧Term ρ₂′ (proj₁ dp) (proj₁ p) , ⟦ apply-term {τ₂} ⟧Term ρ₂′ (proj₂ dp) (proj₂ p))
        ≡
        (⟦ apply-term {τ₁} ⟧Term ρ₁′ (proj₁ dp) (proj₁ p) , ⟦ apply-term {τ₂} ⟧Term ρ₁′ (proj₂ dp) (proj₂ p))
      goal
        rewrite R.meaning-⊕-invariant {τ₁} Γ₁′≼Γ₂′ ρ₂′
        | R.meaning-⊕-invariant {τ₂} Γ₁′≼Γ₂′ ρ₂′ = refl

meaning-⊝-invariant-base base-int Γ₁≼Γ₂ ρ = refl
meaning-⊝-invariant-base base-bag Γ₁≼Γ₂ ρ = refl
meaning-⊝-invariant-base (base-pair τ₁ τ₂) {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ = ext (λ q → ext (goal q))
  where
    module _ (q p : ⟦ _pair_ τ₁ τ₂ ⟧) where
      Γ₁′ Γ₂′ : Context
      Γ₁′ = (_pair_ τ₁ τ₂) • (_pair_ τ₁ τ₂) • Γ₁
      Γ₂′ = (_pair_ τ₁ τ₂) • (_pair_ τ₁ τ₂) • Γ₂
      ρ₂′ : ⟦ Γ₂′ ⟧Context
      ρ₂′ = p • q • ρ
      Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
      Γ₁′≼Γ₂′ = keep _ • keep _ • Γ₁≼Γ₂
      ρ₁′ : ⟦ Γ₁′ ⟧Context
      ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
      explain : ρ₁′ ≡ p • q • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
      explain = refl
      goal :
        (⟦ diff-term {τ₁} ⟧Term ρ₂′ (proj₁ q) (proj₁ p) , ⟦ diff-term {τ₂} ⟧Term ρ₂′ (proj₂ q) (proj₂ p))
        ≡
        (⟦ diff-term {τ₁} ⟧Term ρ₁′ (proj₁ q) (proj₁ p) , ⟦ diff-term {τ₂} ⟧Term ρ₁′ (proj₂ q) (proj₂ p))
      goal
        rewrite R.meaning-⊝-invariant {τ₁} Γ₁′≼Γ₂′ ρ₂′
        | R.meaning-⊝-invariant {τ₂} Γ₁′≼Γ₂′ ρ₂′ = refl

meaning-onil-invariant-base base-int Γ₁≼Γ₂ ρ = refl
meaning-onil-invariant-base base-bag Γ₁≼Γ₂ ρ = refl
meaning-onil-invariant-base (base-pair τ₁ τ₂) {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ = ext goal
  where
    module _ (p : ⟦ _pair_ τ₁ τ₂ ⟧) where
      Γ₁′ Γ₂′ : Context
      Γ₁′ = (_pair_ τ₁ τ₂) • Γ₁
      Γ₂′ = (_pair_ τ₁ τ₂) • Γ₂
      ρ₂′ : ⟦ Γ₂′ ⟧Context
      ρ₂′ = p • ρ
      Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
      Γ₁′≼Γ₂′ = keep _ • Γ₁≼Γ₂
      ρ₁′ : ⟦ Γ₁′ ⟧Context
      ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
      explain : ρ₁′ ≡ p • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
      explain = refl
      goal :
        (⟦ nil-term {τ₁} ⟧Term ρ₂′ (proj₁ p) , ⟦ nil-term {τ₂} ⟧Term ρ₂′ (proj₂ p))
        ≡
        (⟦ nil-term {τ₁} ⟧Term ρ₁′ (proj₁ p) , ⟦ nil-term {τ₂} ⟧Term ρ₁′ (proj₂ p))
      goal
        rewrite R.meaning-onil-invariant {τ₁} Γ₁′≼Γ₂′ ρ₂′
        | R.meaning-onil-invariant {τ₂} Γ₁′≼Γ₂′ ρ₂′ = refl

meaning-⊕-base base-int = refl
meaning-⊕-base base-bag = refl
meaning-⊕-base (base-pair τ₁ τ₂) {Γ = Γ} {t = t} {Δt = Δt} {ρ = ρ}
  rewrite R.meaning-⊕ {τ₁} {Γ} {t = fst t} {Δt = fst Δt} {ρ = ρ}
  | R.meaning-⊕-invariant {τ₁}
    (drop _pair_ τ₁ τ₂ • (drop _pair_ (ΔType τ₁) (ΔType τ₂) • ≼-refl {Γ}))
    (⟦ t ⟧Term ρ • ⟦ Δt ⟧Term ρ • ρ)
  | R.meaning-⊕ {τ₂} {Γ} {t = snd t} {Δt = snd Δt} {ρ = ρ}
  | R.meaning-⊕-invariant {τ₂}
    (drop _pair_ τ₁ τ₂ • (drop _pair_ (ΔType τ₁) (ΔType τ₂) • ≼-refl {Γ}))
    (⟦ t ⟧Term ρ • ⟦ Δt ⟧Term ρ • ρ)
  | ⟦⟧-≼-refl ρ
  = refl

meaning-⊝-base base-int = refl
meaning-⊝-base base-bag = refl
meaning-⊝-base (base-pair τ₁ τ₂) {Γ = Γ} {s = s} {t = t} {ρ = ρ}
  rewrite R.meaning-⊝ {τ₁} {s = fst s} {t = fst t} {ρ = ρ}
  | R.meaning-⊝-invariant {τ₁}
    (drop _pair_ τ₁ τ₂ • drop _pair_ τ₁ τ₂ • ≼-refl {Γ})
    (⟦ t ⟧Term ρ • ⟦ s ⟧Term ρ • ρ)
  | R.meaning-⊝ {τ₂} {s = snd s} {t = snd t} {ρ = ρ}
  | R.meaning-⊝-invariant {τ₂}
    (drop _pair_ τ₁ τ₂ • drop _pair_ τ₁ τ₂ • ≼-refl {Γ})
    (⟦ t ⟧Term ρ • ⟦ s ⟧Term ρ • ρ)
  | ⟦⟧-≼-refl ρ
  = refl

meaning-onil-base base-int = refl
meaning-onil-base base-bag = refl
meaning-onil-base (base-pair τ₁ τ₂) {Γ = Γ} {t = t} {ρ = ρ}
  rewrite R.meaning-onil {τ₁} {t = fst t} {ρ = ρ}
  | R.meaning-onil-invariant {τ₁} (drop _pair_ τ₁ τ₂ • ≼-refl) (⟦ t ⟧Term ρ • ρ)
  | R.meaning-onil {τ₂} {t = snd t} {ρ = ρ}
  | R.meaning-onil-invariant {τ₂} (drop _pair_ τ₁ τ₂ • ≼-refl) (⟦ t ⟧Term ρ • ρ)
  | ⟦⟧-≼-refl ρ
  = refl

open R public
