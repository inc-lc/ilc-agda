module Denotation.Derive.Canon-Popl14 where

-- The denotational properties of the `derive` transformation
-- for Calculus Popl14. In particular, the main theorem
-- about it producing the correct incremental behavior.

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
open import Popl14.Change.Term
open import Popl14.Change.Value
open import Popl14.Change.Evaluation
open import Popl14.Change.Validity
open import Popl14.Change.Derive public
open import Denotation.Implementation.Popl14 public

open import Base.Denotation.Notation
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Popl14
open import Postulate.Extensionality

deriveVar-correct : ∀ {τ Γ} {x : Var Γ τ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧} {C : compatible ρ ρ′} →
  ⟦ x ⟧ΔVar ρ ≈₍ τ ₎ ⟦ deriveVar x ⟧ ρ′

deriveVar-correct {x = this}
  {cons _ _ _ • _} {_ • _ • _} {cons _ Δv≈Δv′ _} = Δv≈Δv′
deriveVar-correct {x = that y}
  {cons _ _ _ • ρ} {_ • _ • ρ′} {cons _ _ C} =
  deriveVar-correct {x = y} {ρ} {ρ′} {C}

-- That `derive t` implements ⟦ t ⟧Δ
derive-correct : ∀ {τ Γ} {t : Term Γ τ}
  {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧} {C : compatible ρ ρ′} →
  ⟦ t ⟧Δ ρ ≈₍ τ ₎ ⟦ derive t ⟧ ρ′

derive-correct {t = intlit n} = refl
derive-correct {t = add s t} {ρ} {ρ′} {C} = cong₂ _+_
  (derive-correct {t = s} {ρ} {ρ′} {C})
  (derive-correct {t = t} {ρ} {ρ′} {C})
derive-correct {t = minus t} {ρ} {ρ′} {C} =
  cong -_ (derive-correct {t = t} {ρ} {ρ′} {C})

derive-correct {t = empty} = refl
derive-correct {t = insert s t} {ρ} {ρ′} {C} =
  cong₂ _\\_
    (cong₂ _++_
      (cong singletonBag (cong₂ _+_
        (⟦fit⟧ s C)
        (derive-correct {t = s} {ρ} {ρ′} {C})))
      (cong₂ _++_
        (⟦fit⟧ t C)
        (derive-correct {t = t} {ρ} {ρ′} {C})))
    (cong₂ _++_ (cong singletonBag (⟦fit⟧ s C)) (⟦fit⟧ t C))
derive-correct {t = union s t} {ρ} {ρ′} {C} = cong₂ _++_
  (derive-correct {t = s} {ρ} {ρ′} {C})
  (derive-correct {t = t} {ρ} {ρ′} {C})
derive-correct {t = negate t} {ρ} {ρ′} {C} =
  cong negateBag (derive-correct {t = t} {ρ} {ρ′} {C})

derive-correct {t = flatmap s t} {ρ} {ρ′} {C} =
  cong₂ _\\_
    (cong₂ flatmapBag
      (ext (λ v →
        cong₂ _++_
          (cong (λ hole → hole v) (⟦fit⟧ s C))
          (derive-correct {t = s} {ρ} {ρ′} {C}
            (nil-valid-change int v) (v - v) refl)))
      (cong₂ _++_
        (⟦fit⟧ t C)
        (derive-correct {t = t} {ρ} {ρ′} {C})))
    (cong₂ flatmapBag (⟦fit⟧ s C) (⟦fit⟧ t C))
derive-correct {t = sum t} {ρ} {ρ′} {C} =
  cong sumBag (derive-correct {t = t} {ρ} {ρ′} {C})

derive-correct {t = var x} {ρ} {ρ′} {C} =
  deriveVar-correct {x = x} {ρ} {ρ′} {C}
derive-correct {t = app s t} {ρ} {ρ′} {C}
  rewrite sym (⟦fit⟧ t C) =
  derive-correct {t = s} {ρ} {ρ′} {C}
  (cons (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ ρ) (validity t ρ))
  (⟦ derive t ⟧ ρ′) (derive-correct {t = t} {ρ} {ρ′} {C})
derive-correct {σ ⇒ τ} {t = abs t} {ρ} {ρ′} {C} =
  λ Δw Δw′ Δw≈Δw′ →
    derive-correct {t = t}
      {Δw • ρ} {Δw′ • before {σ} Δw • ρ′} {cons refl Δw≈Δw′ C}

main-theorem : ∀ {σ τ}
  {f : Term ∅ (σ ⇒ τ)} {x : Term ∅ σ} {y : Term ∅ σ}
  → ⟦ app f y ⟧
  ≡ ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧

main-theorem {σ} {τ} {f} {x} {y} =
  let
    h  = ⟦ f ⟧ ∅
    Δh = ⟦ f ⟧Δ ∅
    Δh′ = ⟦ derive f ⟧ ∅
    v  = ⟦ x ⟧ ∅
    u  = ⟦ y ⟧ ∅
    Δoutput-term = app (app (derive f) x) (y ⊝ x)
  in
    ext {A = ⟦ ∅ ⟧Context} (λ { ∅ →
    begin
      h u
    ≡⟨ cong h (sym (v+[u-v]=u {σ})) ⟩
      h (v ⊞₍ σ ₎ (u ⊟₍ σ ₎ v))
    ≡⟨ corollary-closed {σ} {τ} {f} (diff-valid-change σ u v) ⟩
      h v ⊞₍ τ ₎ Δh (diff-valid-change σ u v)
    ≡⟨ carry-over {τ}
        (cons _ _ (proj₁ (validity f ∅ (diff-valid-change σ u v))))
        (derive-correct {Γ = ∅} {t = f}
          {∅} {∅} (diff-valid-change σ u v) (u ⟦⊝₍ σ ₎⟧ v) (u⊟v≈u⊝v {σ} {u} {v})) ⟩
      h v ⟦⊕₍ τ ₎⟧ Δh′ v (u ⟦⊝₍ σ ₎⟧ v)
    ≡⟨ trans
        (cong (λ hole → h v ⟦⊕₍ τ ₎⟧ Δh′ v hole) (meaning-⊝ {σ} {s = y} {x}))
        (meaning-⊕ {t = app f x} {Δt = Δoutput-term}) ⟩
      ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧ ∅
    ∎}) where open ≡-Reasoning
