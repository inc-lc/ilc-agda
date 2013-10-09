module Denotation.Implementation.Popl14 where

-- Notions of programs being implementations of specifications
-- for Calculus Popl14

open import Popl14.Change.Specification public

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
open import Popl14.Denotation.Evaluation
open import Popl14.Change.Derive
open import Popl14.Change.Value
open import Popl14.Change.Validity

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Tuples
open import Structure.Bag.Popl14
open import Postulate.Extensionality

alternate : ∀ {Γ} → ⟦ Γ ⟧ → ⟦ mapContext ΔType Γ ⟧ → ⟦ ΔContext Γ ⟧
alternate {∅} ∅ ∅ = ∅
alternate {τ • Γ} (v • ρ) (dv • dρ) = dv • v • alternate ρ dρ

infix 4 implements
syntax implements τ u v = u ≈₍ τ ₎ v
implements : ∀ τ {v} → Change τ v → ⟦ ΔType τ ⟧ → Set

implements int {v} Δv Δv′ = Δv ≡ Δv′
implements bag {v} Δv Δv′ = Δv ≡ Δv′
implements (σ ⇒ τ) {f} Δf Δf′ =
  (w : ⟦ σ ⟧) (Δw : Change σ w)
  (Δw′ : ⟦ ΔType σ ⟧) (Δw≈Δw′ : implements σ {w} Δw Δw′) →
  implements τ {f w} (call-change Δf w Δw) (Δf′ w Δw′)

infix 4 _≈_
_≈_ : ∀ {τ v} → Change τ v → ⟦ ΔType τ ⟧ → Set
_≈_ {τ} {v} = implements τ {v}

data implements-env : ∀ Γ → {ρ : ⟦ Γ ⟧} (dρ : ΔEnv Γ ρ) → ⟦ mapContext ΔType Γ ⟧ → Set where
  ∅ : implements-env ∅ {∅} ∅ ∅
  _•_ : ∀ {τ Γ v ρ dv dρ v′ ρ′} →
    (dv≈v′ : implements τ {v} dv v′) →
    (dρ≈ρ′ : implements-env Γ {ρ} dρ ρ′) →
    implements-env (τ • Γ) {v • ρ} (dv • dρ) (v′ • ρ′)

-- If a program implements a specification, then certain things
-- proven about the specification carry over to the programs.
carry-over : ∀ {τ}
  {v : ⟦ τ ⟧}
  (Δv : Change τ v)
  {Δv′ : ⟦ ΔType τ ⟧} (Δv≈Δv′ : Δv ≈₍ τ ₎ Δv′) →
    after {τ} Δv ≡ before {τ} Δv ⟦⊕₍ τ ₎⟧ Δv′

u⊟v≈u⊝v : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
  diff-change τ u v ≈₍ τ ₎ u ⟦⊝₍ τ ₎⟧ v
u⊟v≈u⊝v {base base-int} = refl
u⊟v≈u⊝v {base base-bag} = refl
u⊟v≈u⊝v {σ ⇒ τ} {g} {f} = result where
  result : (w : ⟦ σ ⟧) (Δw : Change σ w) →
    (Δw′ : ⟦ ΔType σ ⟧) → Δw ≈₍ σ ₎ Δw′ →
    diff-change τ (g (after {σ} Δw)) (f (before {σ} Δw)) ≈₍ τ ₎ g (before {σ} Δw ⟦⊕₍ σ ₎⟧ Δw′) ⟦⊝₍ τ ₎⟧ f (before {σ} Δw)
  result w Δw Δw′ Δw≈Δw′
    rewrite carry-over {σ} Δw Δw≈Δw′ =
    u⊟v≈u⊝v {τ} {g (before {σ} Δw ⟦⊕₍ σ ₎⟧ Δw′)} {f (before {σ} Δw)}
carry-over {base base-int} {v} Δv Δv≈Δv′ = cong (_+_ v) Δv≈Δv′
carry-over {base base-bag} Δv Δv≈Δv′ = cong (_++_ (before {bag} Δv)) Δv≈Δv′
carry-over {σ ⇒ τ} {f} Δf {Δf′} Δf≈Δf′ =
  ext (λ v →
    carry-over {τ} {f v} (call-change Δf v (nil-change σ v))
      {Δf′ v (v ⟦⊝₍ σ ₎⟧ v)}
      (Δf≈Δf′ v (nil-change σ v) (v ⟦⊝₍ σ ₎⟧ v) ( u⊟v≈u⊝v {σ} {v} {v})))

-- A property relating `alternate` and the subcontext relation Γ≼ΔΓ
⟦Γ≼ΔΓ⟧ : ∀ {Γ} (ρ : ⟦ Γ ⟧) (dρ : ⟦ mapContext ΔType Γ ⟧) →
  ρ ≡ ⟦ Γ≼ΔΓ ⟧ (alternate ρ dρ)
⟦Γ≼ΔΓ⟧ ∅ ∅ = refl
⟦Γ≼ΔΓ⟧ (v • ρ) (dv • dρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ ρ dρ)

-- A specialization of the soundness of weakening
⟦fit⟧ : ∀ {τ Γ} (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ⟦ mapContext ΔType Γ ⟧) →
  ⟦ t ⟧ ρ ≡ ⟦ fit t ⟧ (alternate ρ dρ)
⟦fit⟧ t ρ dρ =
  trans (cong ⟦ t ⟧ (⟦Γ≼ΔΓ⟧ ρ dρ)) (sym (weaken-sound t _))
