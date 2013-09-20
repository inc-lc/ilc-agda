module Popl14.Denotation.Evaluation where

-- Evaluating terms of Calculus Popl14 into Agda values
--
-- Contents
-- - Semantic brackets
-- - Soundness of weakening of terms
-- - Relating `diff` with `diff-term`, `apply` with `apply-term`

open import Popl14.Change.Term public
open import Denotation.Environment.Popl14 public

open import Data.Integer
open import Structure.Bag.Popl14
open import Postulate.Extensionality
open import Theorem.CongApp

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧

⟦ intlit n ⟧Term ρ = n
⟦ add s t ⟧Term ρ = ⟦ s ⟧Term ρ + ⟦ t ⟧Term ρ
⟦ minus t ⟧Term ρ = - ⟦ t ⟧Term ρ

⟦ empty ⟧Term ρ = emptyBag
⟦ insert s t ⟧Term ρ = singletonBag (⟦ s ⟧Term ρ) ++ ⟦ t ⟧Term ρ
⟦ union s t ⟧Term ρ = ⟦ s ⟧Term ρ ++ ⟦ t ⟧Term ρ
⟦ negate t ⟧Term ρ = negateBag (⟦ t ⟧Term ρ)

⟦ flatmap s t ⟧Term ρ = flatmapBag (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
⟦ sum t ⟧Term ρ = sumBag (⟦ t ⟧Term ρ)

⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ app s t ⟧Term ρ = (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

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
  ⟦ t ⟧ ρ ⟦⊕⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕ Δt ⟧ ρ

meaning-⊝ : ∀ {τ Γ}
  {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
  ⟦ s ⟧ ρ ⟦⊝⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝ t ⟧ ρ

meaning-⊕ {int} = refl
meaning-⊕ {bag} = refl
meaning-⊕ {σ ⇒ τ} {Γ} {t} {Δt} {ρ} = ext (λ v →
  let
    ρ′ : ⟦ σ • (σ ⇒ τ) • ΔType (σ ⇒ τ) • Γ ⟧Context
    ρ′ = v • ⟦ t ⟧ ρ • ⟦ Δt ⟧ ρ • ρ
    x  = var this
    f  = var (that this)
    Δf = var (that (that this))
    y  = app f x
    Δy = app (app Δf x) (x ⊝ x)
  in
    begin
      ⟦ t ⟧ ρ v ⟦⊕⟧ ⟦ Δt ⟧ ρ v (v ⟦⊝⟧ v)
    ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v ⟦⊕⟧ ⟦ Δt ⟧ ρ v hole)
         (meaning-⊝ {s = x} {x} {ρ′}) ⟩
      ⟦ t ⟧ ρ v ⟦⊕⟧ ⟦ Δt ⟧ ρ v (⟦ x ⊝ x ⟧ ρ′)
    ≡⟨ meaning-⊕ {t = y} {Δt = Δy} {ρ′} ⟩
      ⟦ y ⊕ Δy ⟧ ρ′
    ∎) where open ≡-Reasoning

meaning-⊝ {int} = refl
meaning-⊝ {bag} = refl
meaning-⊝ {σ ⇒ τ} {Γ} {s} {t} {ρ} =
  ext (λ v → ext (λ Δv →
  let
    ρ′ : ⟦ ΔType σ • σ • (σ ⇒ τ) • (σ ⇒ τ) • Γ ⟧Context
    ρ′ = Δv • v • ⟦ t ⟧Term ρ • ⟦ s ⟧Term ρ • ρ
    Δx = var this
    x  = var (that this)
    f  = var (that (that this))
    g  = var (that (that (that this)))
    y  = app f x
    y′ = app g (x ⊕ Δx)
  in
    begin
      ⟦ s ⟧ ρ (v ⟦⊕⟧ Δv) ⟦⊝⟧ ⟦ t ⟧ ρ v
    ≡⟨ cong (λ hole → ⟦ s ⟧ ρ hole ⟦⊝⟧ ⟦ t ⟧ ρ v)
         (meaning-⊕ {t = x} {Δt = Δx} {ρ′}) ⟩
      ⟦ s ⟧ ρ (⟦ x ⊕ Δx ⟧ ρ′) ⟦⊝⟧ ⟦ t ⟧ ρ v
    ≡⟨ meaning-⊝ {s = y′} {y} {ρ′} ⟩
      ⟦ y′ ⊝ y ⟧ ρ′
    ∎)) where open ≡-Reasoning
