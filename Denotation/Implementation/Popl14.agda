module Denotation.Implementation.Popl14 where

-- Notions of programs being implementations of specifications
-- for Calculus Popl14

open import Denotation.Specification.Canon-Popl14 public

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
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

infix 4 implements
syntax implements τ u v = u ≈₍ τ ₎ v
implements : ∀ (τ : Type) → Change τ → ⟦ ΔType τ ⟧ → Set

u ≈₍ int ₎ v = u ≡ v
u ≈₍ bag ₎ v = u ≡ v
u ≈₍ σ ⇒ τ ₎ v =
  (Δw : ValidChange σ)
  (Δw′ : ⟦ ΔType σ ⟧) (Δw≈Δw′ : implements σ (change {σ} Δw) Δw′) →
  implements τ (u Δw) (v (before {σ} Δw) Δw′)

infix 4 _≈_
_≈_ : ∀ {τ} → Change τ → ⟦ ΔType τ ⟧ → Set
_≈_ {τ} = implements τ

compatible : ∀ {Γ} → ΔEnv Γ → ⟦ ΔContext Γ ⟧ → Set
compatible {∅} ∅ ∅ = ⊤
compatible {τ • Γ} (cons v Δv _ • ρ) (Δv′ • v′ • ρ′) =
  Triple (v ≡ v′) (λ _ → Δv ≈₍ τ ₎ Δv′) (λ _ _ → compatible ρ ρ′)

-- If a program implements a specification, then certain things
-- proven about the specification carry over to the programs.
carry-over : ∀ {τ}
  (Δv : ValidChange τ)
  {Δv′ : ⟦ ΔType τ ⟧} (Δv≈Δv′ : change {τ} Δv ≈₍ τ ₎ Δv′) →
    after {τ} Δv ≡ before {τ} Δv ⟦⊕₍ τ ₎⟧ Δv′

u⊟v≈u⊝v : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
  u ⊟₍ τ ₎ v ≈₍ τ ₎ u ⟦⊝₍ τ ₎⟧ v
u⊟v≈u⊝v {base base-int} = refl
u⊟v≈u⊝v {base base-bag} = refl
u⊟v≈u⊝v {σ ⇒ τ} {g} {f} = result where
  result : (Δw : ValidChange σ) →
    (Δw′ : ⟦ ΔType σ ⟧) → change {σ} Δw ≈₍ σ ₎ Δw′ →
    g (after {σ} Δw) ⊟₍ τ ₎ f (before {σ} Δw) ≈₍ τ ₎ g (before {σ} Δw ⟦⊕₍ σ ₎⟧ Δw′) ⟦⊝₍ τ ₎⟧ f (before {σ} Δw)
  result Δw Δw′ Δw≈Δw′
    rewrite carry-over {σ} Δw Δw≈Δw′ =
    u⊟v≈u⊝v {τ} {g (before {σ} Δw ⟦⊕₍ σ ₎⟧ Δw′)} {f (before {σ} Δw)}
carry-over {base base-int} Δv Δv≈Δv′ = cong (_+_  (before {int} Δv)) Δv≈Δv′
carry-over {base base-bag} Δv Δv≈Δv′ = cong (_++_ (before {bag} Δv)) Δv≈Δv′
carry-over {σ ⇒ τ} Δf {Δf′} Δf≈Δf′ =
  ext (λ v →
  let
    S = u⊟v≈u⊝v {σ} {v} {v}
  in
    carry-over {τ} (call-valid-change σ τ Δf (nil-valid-change σ v))
      {Δf′ v (v ⟦⊝₍ σ ₎⟧ v)}
      (Δf≈Δf′ (nil-valid-change σ v) (v ⟦⊝₍ σ ₎⟧ v) S))

-- A property relating `ignore` and the subcontext relation Γ≼ΔΓ
⟦Γ≼ΔΓ⟧ : ∀ {Γ} {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧}
  (C : compatible ρ ρ′) → ignore ρ ≡ ⟦ Γ≼ΔΓ ⟧ ρ′
⟦Γ≼ΔΓ⟧ {∅} {∅} {∅} _ = refl
⟦Γ≼ΔΓ⟧ {τ • Γ} {cons v dv _ • ρ} {dv′ • v′ • ρ′}
  (cons v≡v′ _ C) = cong₂ _•_ v≡v′ (⟦Γ≼ΔΓ⟧ C)

-- A specialization of the soundness of weakening
⟦fit⟧ : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧} (C : compatible ρ ρ′) →
  ⟦ t ⟧ (ignore ρ) ≡ ⟦ fit t ⟧ ρ′
⟦fit⟧ t {ρ} {ρ′} C =
  trans (cong ⟦ t ⟧ (⟦Γ≼ΔΓ⟧ C)) (sym (weaken-sound t ρ′))
