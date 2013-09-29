module Popl14.Change.Evaluation where

open import Popl14.Syntax.Type
open import Popl14.Syntax.Term
open import Popl14.Change.Type
open import Popl14.Change.Term
open import Popl14.Change.Value
open import Popl14.Denotation.Value
open import Popl14.Denotation.Evaluation

open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation

open import Postulate.Extensionality

-- unique names with unambiguous types
-- to help type inference figure things out
private
  module Disambiguation where
    infixr 9 _⋆_
    _⋆_ : Type → Context → Context
    _⋆_ = _•_

-- Relating `diff` with `diff-term`, `apply` with `apply-term`
meaning-⊕ : ∀ {τ Γ}
  {t : Term Γ τ} {Δt : Term Γ (ΔType τ)} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕₍ τ ₎ Δt ⟧ ρ

meaning-⊝ : ∀ {τ Γ}
  {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
  ⟦ s ⟧ ρ ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝ t ⟧ ρ

meaning-⊕ {base base-int} = refl
meaning-⊕ {base base-bag} = refl
meaning-⊕ {σ ⇒ τ} {Γ} {t} {Δt} {ρ} = ext (λ v →
  let
    Γ′ = σ ⋆ (σ ⇒ τ) ⋆ ΔType (σ ⇒ τ) ⋆ Γ
    ρ′ : ⟦ Γ′ ⟧
    ρ′ = v • (⟦ t ⟧ ρ) • (⟦ Δt ⟧ ρ) • ρ
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
      ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (v ⟦⊝₍ σ ₎⟧ v)
    ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v hole)
         (meaning-⊝ {s = x} {x} {ρ′}) ⟩
      ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (⟦ x ⊝ x ⟧ ρ′)
    ≡⟨ meaning-⊕ {t = y} {Δt = Δy} {ρ′} ⟩
      ⟦ y ⊕₍ τ ₎ Δy ⟧ ρ′
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
    y′ = app g (x ⊕₍ σ ₎ Δx)
  in
    begin
      ⟦ s ⟧ ρ (v ⟦⊕₍ σ ₎⟧ Δv) ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v
    ≡⟨ cong (λ hole → ⟦ s ⟧ ρ hole ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v)
         (meaning-⊕ {t = x} {Δt = Δx} {ρ′}) ⟩
      ⟦ s ⟧ ρ (⟦ x ⊕₍ σ ₎ Δx ⟧ ρ′) ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ v
    ≡⟨ meaning-⊝ {s = y′} {y} {ρ′} ⟩
      ⟦ y′ ⊝ y ⟧ ρ′
    ∎))
  where
    open ≡-Reasoning
    open Disambiguation
