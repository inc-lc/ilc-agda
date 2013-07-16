module Denotation.Implementation.Popl14 where

-- Notions of programs being implementations of specifications
-- for Calculus Popl14

open import Denotation.Specification.Canon-Popl14 public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Popl14
open import Postulate.Extensionality

-- Better name for v ≈ ⟦ t ⟧:
-- t implements v.
infix 4 _≈_
_≈_ : ∀ {τ} → ΔVal τ → ⟦ ΔType τ ⟧ → Set
_≈_ {int} u v = u ≡ v
_≈_ {bag} u v = u ≡ v
_≈_ {σ ⇒ τ} u v = 
  (w : ⟦ σ ⟧) (Δw : ΔVal σ) (Δw′ : ⟦ ΔType σ ⟧)
  (R[w,Δw] : valid w Δw) (Δw≈Δw′ : Δw ≈ Δw′) →
  u w Δw R[w,Δw] ≈ v w Δw′

compatible : ∀ {Γ} → ΔEnv Γ → ⟦ ΔContext Γ ⟧ → Set
compatible {∅} ∅ ∅ = ⊤
compatible {τ • Γ} (cons v Δv _ ρ) (Δv′ • v′ • ρ′) =
  Triple (v ≡ v′) (λ _ → Δv ≈ Δv′) (λ _ _ → compatible ρ ρ′)

-- If a program implements a specification, then certain things
-- proven about the specification carry over to the programs.
carry-over : ∀ {τ}
  {v : ⟦ τ ⟧} {Δv : ΔVal τ} {Δv′ : ⟦ ΔType τ ⟧}
 (R[v,Δv] : valid v Δv) (Δv≈Δv′ : Δv ≈ Δv′) →
  v ⊞ Δv ≡ v ⟦⊕⟧ Δv′

u⊟v≈u⊝v : ∀ {τ : Type} {u v : ⟦ τ ⟧} → u ⊟ v ≈ u ⟦⊝⟧ v
u⊟v≈u⊝v {int} = refl
u⊟v≈u⊝v {bag} = refl
u⊟v≈u⊝v {σ ⇒ τ} {g} {f} = result where
  result : (w : ⟦ σ ⟧) (Δw : ΔVal σ) (Δw′ : ⟦ ΔType σ ⟧) →
    valid w Δw → Δw ≈ Δw′ →
    g (w ⊞ Δw) ⊟ f w ≈ g (w ⟦⊕⟧ Δw′) ⟦⊝⟧ f w
  result w Δw Δw′ R[w,Δw] Δw≈Δw′
    rewrite carry-over {v = w} R[w,Δw] Δw≈Δw′ =
    u⊟v≈u⊝v {u = g (w ⟦⊕⟧ Δw′)} {f w}
carry-over {int} {v} tt Δv≈Δv′ = cong (_+_  v) Δv≈Δv′
carry-over {bag} {v} tt Δv≈Δv′ = cong (_++_ v) Δv≈Δv′
carry-over {σ ⇒ τ} {f} {Δf} {Δf′} R[f,Δf] Δf≈Δf′ =
  ext (λ v →
  let
    V = R[v,u-v] {u = v} {v}
    S = u⊟v≈u⊝v {u = v} {v}
  in
    carry-over {τ} {f v}
      {Δf v (v ⊟ v) V} {Δf′ v (v ⟦⊝⟧ v)}
      (proj₁ (R[f,Δf] v (v ⊟ v) V))
      (Δf≈Δf′ v (v ⊟ v) (v ⟦⊝⟧ v) V S))

-- A property relating `ignore` and the subcontext relation Γ≼ΔΓ
⟦Γ≼ΔΓ⟧ : ∀ {Γ} {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧}
  (C : compatible ρ ρ′) → ignore ρ ≡ ⟦ Γ≼ΔΓ ⟧ ρ′
⟦Γ≼ΔΓ⟧ {∅} {∅} {∅} _ = refl
⟦Γ≼ΔΓ⟧ {τ • Γ} {cons v dv _ ρ} {dv′ • v′ • ρ′}
  (cons v≡v′ _ C) = cong₂ _•_ v≡v′ (⟦Γ≼ΔΓ⟧ C)

-- A specialization of the soundness of weakening
⟦fit⟧ : ∀ {τ Γ} (t : Term Γ τ)
  {ρ : ΔEnv Γ} {ρ′ : ⟦ ΔContext Γ ⟧} (C : compatible ρ ρ′) →
  ⟦ t ⟧ (ignore ρ) ≡ ⟦ fit t ⟧ ρ′
⟦fit⟧ t {ρ} {ρ′} C =
  trans (cong ⟦ t ⟧ (⟦Γ≼ΔΓ⟧ C)) (sym (weaken-sound t ρ′))
