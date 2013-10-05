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
  (w : ⟦ σ ⟧) (Δw : Change σ) (R[w,Δw] : valid {σ} w Δw)
  (Δw′ : ⟦ ΔType σ ⟧) (Δw≈Δw′ : implements σ Δw Δw′) →
  implements τ (u (cons w Δw R[w,Δw])) (v w Δw′)

infix 4 _≈_
_≈_ : ∀ {τ} → Change τ → ⟦ ΔType τ ⟧ → Set
_≈_ {τ} = implements τ

module Disambiguation (τ : Type) where
  _✚_ : ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  _✚_ = _⟦⊕⟧_ {τ}
  _−_ : ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  _−_ = _⟦⊝⟧_ {τ}
  infixl 6 _✚_ _−_
  _≃_ : Change τ → ⟦ ΔType τ ⟧ → Set
  _≃_ = _≈_ {τ}
  infix 4 _≃_

module FunctionDisambiguation (σ : Type) (τ : Type) where
  open Disambiguation (σ ⇒ τ) public
  _✚₁_ : ⟦ τ ⟧ → ⟦ ΔType τ ⟧ → ⟦ τ ⟧
  _✚₁_ = _⟦⊕⟧_ {τ}
  _−₁_ : ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ ΔType τ ⟧
  _−₁_ = _⟦⊝⟧_ {τ}
  infixl 6 _✚₁_ _−₁_
  _≃₁_ : Change τ → ⟦ ΔType τ ⟧ → Set
  _≃₁_ = _≈_ {τ}
  infix 4 _≃₁_
  _✚₀_ : ⟦ σ ⟧ → ⟦ ΔType σ ⟧ → ⟦ σ ⟧
  _✚₀_ = _⟦⊕⟧_ {σ}
  _−₀_ : ⟦ σ ⟧ → ⟦ σ ⟧ → ⟦ ΔType σ ⟧
  _−₀_ = _⟦⊝⟧_ {σ}
  infixl 6 _✚₀_ _−₀_
  _≃₀_ : Change σ → ⟦ ΔType σ ⟧ → Set
  _≃₀_ = _≈_ {σ}
  infix 4 _≃₀_

compatible : ∀ {Γ} → ΔEnv Γ → ⟦ ΔContext Γ ⟧ → Set
compatible {∅} ∅ ∅ = ⊤
compatible {τ • Γ} (cons v Δv _ • ρ) (Δv′ • v′ • ρ′) =
  Triple (v ≡ v′) (λ _ → Δv ≈₍ τ ₎ Δv′) (λ _ _ → compatible ρ ρ′)

-- If a program implements a specification, then certain things
-- proven about the specification carry over to the programs.
carry-over : ∀ {τ}
  (Δv : ValidChange τ)
  {Δv′ : ⟦ ΔType τ ⟧} (Δv≈Δv′ : change {τ} Δv ≈₍ τ ₎ Δv′) →
 let open Disambiguation τ in
   after {τ} Δv ≡ before {τ} Δv ✚ Δv′

u⊟v≈u⊝v : ∀ {τ : Type} {u v : ⟦ τ ⟧} →
  let open Disambiguation τ in
    u ⊟₍ τ ₎ v ≃ u − v
u⊟v≈u⊝v {base base-int} = refl
u⊟v≈u⊝v {base base-bag} = refl
u⊟v≈u⊝v {σ ⇒ τ} {g} {f} = result where
  open FunctionDisambiguation σ τ
  result : (w : ⟦ σ ⟧) (Δw : Change σ) → valid {σ} w Δw →
    (Δw′ : ⟦ ΔType σ ⟧) → Δw ≈₍ σ ₎ Δw′ →
    g (w ⊞₍ σ ₎ Δw) ⊟₍ τ ₎ f w ≃₁ g (w ✚₀ Δw′) −₁ f w
  result w Δw R[w,Δw] Δw′ Δw≈Δw′
    rewrite carry-over {σ} (cons w Δw R[w,Δw]) Δw≈Δw′ =
    u⊟v≈u⊝v {τ} {g (w ✚₀ Δw′)} {f w}
carry-over {base base-int} Δv Δv≈Δv′ = cong (_+_  (before {int} Δv)) Δv≈Δv′
carry-over {base base-bag} Δv Δv≈Δv′ = cong (_++_ (before {bag} Δv)) Δv≈Δv′
carry-over {σ ⇒ τ} Δf {Δf′} Δf≈Δf′ =
  ext (λ v →
  let
    open FunctionDisambiguation σ τ
    V = R[v,u-v] {σ} {v} {v}
    S = u⊟v≈u⊝v {σ} {v} {v}
  in
    carry-over {τ} (call-valid-change σ τ Δf (nil-valid-change σ v))
      {Δf′ v (v −₀ v)}
      (Δf≈Δf′ v (v ⊟₍ σ ₎ v) V (v −₀ v) S))

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
