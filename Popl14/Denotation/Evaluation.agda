module Popl14.Denotation.Evaluation where

-- Evaluating terms of Calculus Popl14 into Agda values
--
-- Contents
-- - Semantic brackets
-- - Soundness of weakening of terms
-- - Relating `diff` with `diff-term`, `apply` with `apply-term`

open import Popl14.Change.Term public

-- TODO: MOVE!
open import Denotation.Environment.Popl14 public -- MUST BE PUBLIC??

-- TODO: REPLACE PREVIOUS IMPORT BY THE FOLLOWING TWO:
--open import Popl14.Denotation.Value public
-- open import Base.Denotation.Environment Type ⟦_⟧Type

open import Data.Integer
open import Structure.Bag.Popl14
open import Postulate.Extensionality
open import Theorem.CongApp

open import Parametric.Denotation.Evaluation Const ⟦_⟧Base

⟦_⟧Const : Structure
⟦ intlit-const n ⟧Const ∅ = n
⟦ add-const ⟧Const (m • n • ∅) = m + n
⟦ minus-const ⟧Const (n • ∅) = - n
⟦ empty-const ⟧Const ∅ = emptyBag
⟦ insert-const ⟧Const (n • b • ∅) = singletonBag n ++ b
⟦ union-const ⟧Const (b₁ • b₂ • ∅) = b₁ ++ b₂
⟦ negate-const ⟧Const (b • ∅) = negateBag b
⟦ flatmap-const ⟧Const (f • b • ∅) = flatmapBag f b
⟦ sum-const ⟧Const (b • ∅) = sumBag b

open Structure ⟦_⟧Const public

-- unique names with unambiguous types
-- to help type inference figure things out
private
  module Disambiguation where
    infixr 9 _⋆_
    _⋆_ : Type → Context → Context
    _⋆_ = _•_

weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂} (t : Term Γ₁ τ) →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ₁≼Γ₂ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ₁≼Γ₂ ⟧ ρ)

weaken-sound (intlit n) ρ = refl
weaken-sound (add s t) ρ =
  cong₂ _+_ (weaken-sound s ρ) (weaken-sound t ρ)
weaken-sound (minus t) ρ = cong -_ (weaken-sound t ρ)

weaken-sound empty ρ = refl
weaken-sound (insert s t) ρ =
  cong₂ _++_
    (cong singletonBag (weaken-sound s ρ))
    (weaken-sound t ρ)
weaken-sound (union s t) ρ =
  cong₂ _++_ (weaken-sound s ρ) (weaken-sound t ρ)
weaken-sound (negate t) ρ = cong negateBag (weaken-sound t ρ)

weaken-sound (flatmap s t) ρ =
  cong₂ flatmapBag (weaken-sound s ρ) (weaken-sound t ρ)
weaken-sound (sum t) ρ = cong sumBag (weaken-sound t ρ)

weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weakenVar-sound Γ₁≼Γ₂ x ρ
weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))

-- Relating `diff` with `diff-term`, `apply` with `apply-term`
meaning-⊕ : ∀ {τ Γ}
  {t : Term Γ τ} {Δt : Term Γ (ΔType τ)} {ρ : ⟦ Γ ⟧} →
  let
    _+_ = _⟦⊕⟧_ {τ}
  in
    ⟦ t ⟧ ρ + ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕ Δt ⟧ ρ

meaning-⊝ : ∀ {τ Γ}
  {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
  let
    _-_ = _⟦⊝⟧_ {τ}
  in
    ⟦ s ⟧ ρ - ⟦ t ⟧ ρ ≡ ⟦ s ⊝ t ⟧ ρ

meaning-⊕ {base base-int} = refl
meaning-⊕ {base base-bag} = refl
meaning-⊕ {σ ⇒ τ} {Γ} {t} {Δt} {ρ} = ext (λ v →
  let
    Γ′ = σ ⋆ (σ ⇒ τ) ⋆ ΔType (σ ⇒ τ) ⋆ Γ
    ρ′ : ⟦ Γ′ ⟧
    ρ′ = v • (⟦ t ⟧ ρ) • (⟦ Δt ⟧ ρ) • ρ
    _-₀_ = _⟦⊝⟧_ {σ}
    _+₁_ = _⟦⊕⟧_ {τ}
    x  : Term Γ′ σ
    x  = var this
    f  : Term Γ′ (σ ⇒ τ)
    f  = var (that this)
    Δf : Term Γ′ (ΔType (σ ⇒ τ))
    Δf = var (that (that this))
    y  = app f x
    Δy = app (app Δf x) (x ⊝ x)
  in
    begin
      ⟦ t ⟧ ρ v +₁ ⟦ Δt ⟧ ρ v (v -₀ v)
    ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v +₁ ⟦ Δt ⟧ ρ v hole)
         (meaning-⊝ {s = x} {x} {ρ′}) ⟩
      ⟦ t ⟧ ρ v +₁ ⟦ Δt ⟧ ρ v (⟦ x ⊝ x ⟧ ρ′)
    ≡⟨ meaning-⊕ {t = y} {Δt = Δy} {ρ′} ⟩
      ⟦ y ⊕ Δy ⟧ ρ′
    ∎)
  where
    open ≡-Reasoning
    open Disambiguation

meaning-⊝ {int} = refl
meaning-⊝ {bag} = refl
meaning-⊝ {σ ⇒ τ} {Γ} {s} {t} {ρ} =
  ext (λ v → ext (λ Δv →
  let
    Γ′ = ΔType σ ⋆ σ ⋆ (σ ⇒ τ) ⋆ (σ ⇒ τ) ⋆ Γ
    ρ′ : ⟦ Γ′ ⟧Context
    ρ′ = Δv • v • ⟦ t ⟧Term ρ • ⟦ s ⟧Term ρ • ρ
    Δx : Term Γ′ (ΔType σ)
    Δx = var this
    x  : Term Γ′ σ
    x  = var (that this)
    f  : Term Γ′ (σ ⇒ τ)
    f  = var (that (that this))
    g  : Term Γ′ (σ ⇒ τ)
    g  = var (that (that (that this)))
    y  = app f x
    y′ = app g (x ⊕ Δx)
    _+₀_ = _⟦⊕⟧_ {σ}
    _-₁_ = _⟦⊝⟧_ {τ}
  in
    begin
      ⟦ s ⟧ ρ (v +₀ Δv) -₁ ⟦ t ⟧ ρ v
    ≡⟨ cong (λ hole → ⟦ s ⟧ ρ hole -₁ ⟦ t ⟧ ρ v)
         (meaning-⊕ {t = x} {Δt = Δx} {ρ′}) ⟩
      ⟦ s ⟧ ρ (⟦ x ⊕ Δx ⟧ ρ′) -₁ ⟦ t ⟧ ρ v
    ≡⟨ meaning-⊝ {s = y′} {y} {ρ′} ⟩
      ⟦ y′ ⊝ y ⟧ ρ′
    ∎))
  where
    open ≡-Reasoning
    open Disambiguation
