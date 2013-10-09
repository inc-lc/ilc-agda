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

deriveVar-correct : ∀ {τ Γ} (x : Var Γ τ)
  (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
  ⟦ x ⟧ΔVar ρ dρ ≈₍ τ ₎ ⟦ deriveVar x ⟧ (alternate ρ ρ′)

deriveVar-correct this (v • ρ) (dv • dρ) (dv′ • dρ′) (dv≈dv′ • dρ≈dρ′) = dv≈dv′
deriveVar-correct (that x) (v • ρ) (dv • dρ) (dv′ • dρ′) (dv≈dv′ • dρ≈dρ′) = deriveVar-correct x ρ dρ dρ′ dρ≈dρ′

-- That `derive t` implements ⟦ t ⟧Δ
derive-correct : ∀ {τ Γ} (t : Term Γ τ)
  (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) (ρ′ : ⟦ mapContext ΔType Γ ⟧) (dρ≈ρ′ : implements-env Γ dρ ρ′) →
  ⟦ t ⟧Δ ρ dρ ≈₍ τ ₎ ⟦ derive t ⟧ (alternate ρ ρ′)

derive-correct (intlit n) ρ dρ ρ′ dρ≈ρ′ = refl
derive-correct (add s t) ρ dρ ρ′ dρ≈ρ′ = cong₂ _+_
  (derive-correct s ρ dρ ρ′ dρ≈ρ′)
  (derive-correct t ρ dρ ρ′ dρ≈ρ′)
derive-correct (minus t) ρ dρ ρ′ dρ≈ρ′ =
  cong -_ (derive-correct t ρ dρ ρ′ dρ≈ρ′)

derive-correct empty ρ dρ ρ′ dρ≈ρ′ = refl
derive-correct (insert s t) ρ dρ ρ′ dρ≈ρ′ =
  cong₂ _\\_
    (cong₂ _++_
      (cong singletonBag (cong₂ _+_
        (⟦fit⟧ s ρ ρ′)
        (derive-correct s ρ dρ ρ′ dρ≈ρ′)))
      (cong₂ _++_
        (⟦fit⟧ t ρ ρ′)
        (derive-correct t ρ dρ ρ′ dρ≈ρ′)))
    (cong₂ _++_ (cong singletonBag (⟦fit⟧ s ρ ρ′)) (⟦fit⟧ t ρ ρ′))
derive-correct (union s t) ρ dρ ρ′ dρ≈ρ′ = cong₂ _++_
  (derive-correct s ρ dρ ρ′ dρ≈ρ′)
  (derive-correct t ρ dρ ρ′ dρ≈ρ′)
derive-correct (negate t) ρ dρ ρ′ dρ≈ρ′ =
  cong negateBag (derive-correct t ρ dρ ρ′ dρ≈ρ′)

derive-correct (flatmap s t) ρ dρ ρ′ dρ≈ρ′ =
  cong₂ _\\_
    (cong₂ flatmapBag
      (ext (λ v →
        cong₂ _++_
          (cong (λ hole → hole v) (⟦fit⟧ s ρ ρ′))
            (derive-correct s ρ dρ ρ′ dρ≈ρ′ v (nil-change int v) (v - v) refl)))
      (cong₂ _++_
        (⟦fit⟧ t ρ ρ′)
        (derive-correct t ρ dρ ρ′ dρ≈ρ′)))
    (cong₂ flatmapBag (⟦fit⟧ s ρ ρ′) (⟦fit⟧ t ρ ρ′))
derive-correct (sum t) ρ dρ ρ′ dρ≈ρ′ =
  cong sumBag (derive-correct t ρ dρ ρ′ dρ≈ρ′)

derive-correct (var x) ρ dρ ρ′ dρ≈ρ′ =
  deriveVar-correct x ρ dρ ρ′ dρ≈ρ′
derive-correct (app s t) ρ dρ ρ′ dρ≈ρ′
  rewrite sym (⟦fit⟧ t ρ ρ′) =
    derive-correct s ρ dρ ρ′ dρ≈ρ′
    (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ) (⟦ derive t ⟧ (alternate ρ ρ′)) (derive-correct t ρ dρ ρ′ dρ≈ρ′)

derive-correct (abs {σ} {τ} t) ρ dρ ρ′ dρ≈ρ′ =
  λ w dw w′ dw≈w′ →
    derive-correct t (w • ρ) (dw • dρ) (w′ • ρ′) (dw≈w′ • dρ≈ρ′)

main-theorem : ∀ {σ τ}
  {f : Term ∅ (σ ⇒ τ)} {x : Term ∅ σ} {y : Term ∅ σ}
  → ⟦ app f y ⟧
  ≡ ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧

main-theorem {σ} {τ} {f} {x} {y} =
  let
    h  = ⟦ f ⟧ ∅
    Δh = ⟦ f ⟧Δ ∅ ∅
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
    ≡⟨ corollary-closed {σ} {τ} f v (u ⊟₍ σ ₎ v) ⟩
      h v ⊞₍ τ ₎ call-change Δh v (u ⊟₍ σ ₎ v)
    ≡⟨ carry-over {τ}
        (call-change Δh v (u ⊟₍ σ ₎ v))
        (derive-correct f
          ∅ ∅ ∅ ∅ v (u ⊟₍ σ ₎ v) (u ⟦⊝₍ σ ₎⟧ v) (u⊟v≈u⊝v {σ} {u} {v})) ⟩
      h v ⟦⊕₍ τ ₎⟧ Δh′ v (u ⟦⊝₍ σ ₎⟧ v)
    ≡⟨ trans
        (cong (λ hole → h v ⟦⊕₍ τ ₎⟧ Δh′ v hole) (meaning-⊝ {σ} {s = y} {x}))
        (meaning-⊕ {t = app f x} {Δt = Δoutput-term}) ⟩
      ⟦ app f x ⊕₍ τ ₎ app (app (derive f) x) (y ⊝ x) ⟧ ∅
    ∎}) where open ≡-Reasoning
