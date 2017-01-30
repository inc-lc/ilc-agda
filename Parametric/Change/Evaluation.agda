------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Connecting Parametric.Change.Term and Parametric.Change.Value.
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Change.Type as ChangeType
import Parametric.Change.Term as ChangeTerm
import Parametric.Change.Value as ChangeValue

module Parametric.Change.Evaluation
    {Base : Type.Structure}
    {Const : Term.Structure Base}
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    (ΔBase : ChangeType.Structure Base)
    (apply-base : ChangeTerm.ApplyStructure Const ΔBase)
    (diff-base : ChangeTerm.DiffStructure Const ΔBase)
    (nil-base : ChangeTerm.NilStructure Const ΔBase)
    (⟦apply-base⟧ : ChangeValue.ApplyStructure Const ⟦_⟧Base ΔBase)
    (⟦diff-base⟧ : ChangeValue.DiffStructure Const ⟦_⟧Base ΔBase)
    (⟦nil-base⟧ : ChangeValue.NilStructure Const ⟦_⟧Base ΔBase)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open ChangeType.Structure Base ΔBase
open ChangeTerm.Structure Const ΔBase apply-base diff-base nil-base
open ChangeValue.Structure Const ⟦_⟧Base ΔBase ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧

open import Relation.Binary.PropositionalEquality
open import Base.Denotation.Notation
open import Postulate.Extensionality

-- Extension point 1: Relating ⊕ and its value on base types
ApplyStructure : Set
ApplyStructure = ∀ ι {Γ} →
  {t : Term Γ (base ι)} {Δt : Term Γ (ΔType (base ι))} {ρ : ⟦ Γ ⟧} →
  ⟦ t ⟧ ρ ⟦⊕₍ base ι ₎⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕₍ base ι ₎ Δt ⟧ ρ

-- Extension point 2: Relating ⊝ and its value on base types
DiffStructure : Set
DiffStructure = ∀ ι {Γ} →
  {s : Term Γ (base ι)} {t : Term Γ (base ι)} {ρ : ⟦ Γ ⟧} →
  ⟦ s ⟧ ρ ⟦⊝₍ base ι ₎⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝₍ base ι ₎ t ⟧ ρ

-- Extension point 3: Relating nil-term and its value on base types
NilStructure : Set
NilStructure = ∀ ι {Γ} →
  {t : Term Γ (base ι)} {ρ : ⟦ Γ ⟧} →
  ⟦nil₍ base ι ₎⟧ (⟦ t ⟧ ρ) ≡ ⟦ onil₍ base ι ₎ t ⟧ ρ

DiffInvariantStructure : Set
DiffInvariantStructure =
  ∀ ι {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
  ⟦ diff-base {ι} {Γ₂} ⟧Term ρ ≡ ⟦ diff-base {ι} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)

ApplyInvariantStructure : Set
ApplyInvariantStructure =
  ∀ ι {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
  ⟦ apply-base {ι} {Γ₂} ⟧Term ρ ≡ ⟦ apply-base {ι} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)

NilInvariantStructure : Set
NilInvariantStructure =
  ∀ ι {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
  ⟦ nil-base {ι} {Γ₂} ⟧Term ρ ≡ ⟦ nil-base {ι} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)

record Structure : Set where
  field
    meaning-⊕-base    : ApplyStructure
    meaning-⊝-base    : DiffStructure
    meaning-onil-base : NilStructure
    meaning-⊕-invariant-base : ApplyInvariantStructure
    meaning-⊝-invariant-base : DiffInvariantStructure
    meaning-onil-invariant-base : NilInvariantStructure

  -- unique names with unambiguous types
  -- to help type inference figure things out
  private
    module Disambiguation where
      infixr 9 _⋆_
      _⋆_ : Type → Context → Context
      _⋆_ = _•_

  -- We provide: Relating ⊕ and ⊝ and their values on arbitrary types.
  meaning-⊕ : ∀ {τ Γ}
    {t : Term Γ τ} {Δt : Term Γ (ΔType τ)} {ρ : ⟦ Γ ⟧} →
    ⟦ t ⟧ ρ ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ ≡ ⟦ t ⊕₍ τ ₎ Δt ⟧ ρ

  meaning-⊝ : ∀ {τ Γ}
    {s : Term Γ τ} {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
    ⟦ s ⟧ ρ ⟦⊝₍ τ ₎⟧ ⟦ t ⟧ ρ ≡ ⟦ s ⊝₍ τ ₎ t ⟧ ρ

  meaning-onil : ∀ {τ Γ}
    {t : Term Γ τ} {ρ : ⟦ Γ ⟧} →
    ⟦nil₍ τ ₎⟧ (⟦ t ⟧ ρ) ≡ ⟦ onil₍ τ ₎ t ⟧ ρ

  meaning-⊕ {base ι} {Γ} {τ} {Δt} {ρ} = meaning-⊕-base ι {Γ} {τ} {Δt} {ρ}
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
      Δy = app (app Δf x) (onil x)
    in
      begin
        ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (⟦nil₍ σ ₎⟧ v)
      ≡⟨ cong (λ hole → ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v hole)
           (meaning-onil {t = x} {ρ′}) ⟩
        ⟦ t ⟧ ρ v ⟦⊕₍ τ ₎⟧ ⟦ Δt ⟧ ρ v (⟦ onil x ⟧ ρ′)
      ≡⟨ meaning-⊕ {t = y} {Δt = Δy} {ρ′} ⟩
        ⟦ y ⊕₍ τ ₎ Δy ⟧ ρ′
      ∎)
    where
      open ≡-Reasoning
      open Disambiguation

  open import Postulate.Extensionality

  meaning-onil-invariant :
    ∀ {τ} {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
    ⟦ nil-term {τ} {Γ₂} ⟧Term ρ ≡ ⟦ nil-term {τ} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
  meaning-⊕-invariant :
    ∀ {τ} {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
    ⟦ apply-term {τ} {Γ₂} ⟧Term ρ ≡ ⟦ apply-term {τ} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
  meaning-⊝-invariant :
    ∀ {τ} {Γ₁ Γ₂} (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) ρ →
    ⟦ diff-term {τ} {Γ₂} ⟧Term ρ ≡ ⟦ diff-term {τ} {Γ₁} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ)

  meaning-⊝-invariant {base ι} = meaning-⊝-invariant-base ι
  meaning-⊝-invariant {σ ⇒ τ} {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ =
    ext³ (λ g f v → ext (λ dv →
      let
        Γ₁′ = ΔType σ • σ • (σ ⇒ τ) • (σ ⇒ τ) • Γ₁
        Γ₂′ = ΔType σ • σ • (σ ⇒ τ) • (σ ⇒ τ) • Γ₂
        ρ₂′ : ⟦ Γ₂′ ⟧Context
        ρ₂′ = dv • v • f • g • ρ
        Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
        Γ₁′≼Γ₂′ = keep _ • keep _ • keep _ • keep _ • Γ₁≼Γ₂
        ρ₁′ : ⟦ Γ₁′ ⟧Context
        ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
        explain : ρ₁′ ≡ dv • v • f • g • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
        explain = refl
      in
      begin
        ⟦ diff-term {σ ⇒ τ} ⟧Term ρ g f v dv
      ≡⟨⟩
        ⟦ diff-term {τ} ⟧Term ρ₂′
        (g (⟦ apply-term {σ} ⟧Term ρ₂′ dv v)) (f v)
      ≡⟨ cong₂ (λ h1 h2 → h1 (g (h2 dv v)) (f v)) (meaning-⊝-invariant {τ} Γ₁′≼Γ₂′ ρ₂′) (meaning-⊕-invariant {σ} Γ₁′≼Γ₂′ ρ₂′) ⟩
        ⟦ diff-term {τ} ⟧Term ρ₁′
        (g (⟦ apply-term {σ} ⟧Term ρ₁′ dv v)) (f v)
      ≡⟨⟩
        ⟦ diff-term {σ ⇒ τ} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ) g f v dv
      ∎))
    where
      open ≡-Reasoning

  meaning-onil-invariant {base ι} = meaning-onil-invariant-base ι
  meaning-onil-invariant {σ ⇒ τ} {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ =
    ext³ (λ f v dv →
      let
        Γ₁′ = ΔType σ • σ • (σ ⇒ τ) • (σ ⇒ τ) • Γ₁
        Γ₂′ = ΔType σ • σ • (σ ⇒ τ) • (σ ⇒ τ) • Γ₂
        ρ₂′ : ⟦ Γ₂′ ⟧Context
        ρ₂′ = dv • v • f • f • ρ
        Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
        Γ₁′≼Γ₂′ = keep _ • keep _ • keep _ • keep _ • Γ₁≼Γ₂
        ρ₁′ : ⟦ Γ₁′ ⟧Context
        ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
        explain : ρ₁′ ≡ dv • v • f • f • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
        explain = refl
      in
      begin
        ⟦ nil-term {σ ⇒ τ} ⟧Term ρ f v dv
      ≡⟨⟩
        ⟦ diff-term {τ} ⟧Term ρ₂′ (f (⟦ apply-term {σ} ⟧Term ρ₂′ dv v)) (f v)
      ≡⟨ cong₂ (λ h1 h2 → h1 (f (h2 dv v)) (f v)) (meaning-⊝-invariant {τ} Γ₁′≼Γ₂′ ρ₂′) (meaning-⊕-invariant {σ} Γ₁′≼Γ₂′ ρ₂′) ⟩
        ⟦ diff-term {τ} ⟧Term ρ₁′ (f (⟦ apply-term {σ} ⟧Term ρ₁′ dv v)) (f v)
      ≡⟨⟩
        ⟦ nil-term {σ ⇒ τ} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ) f v dv
      ∎)
    where
      open ≡-Reasoning

  meaning-⊕-invariant {base ι} = meaning-⊕-invariant-base ι
  meaning-⊕-invariant {σ ⇒ τ} {Γ₁} {Γ₂} Γ₁≼Γ₂ ρ =
    ext³ (λ df f v →
      let
        Γ₁′ = σ • (σ ⇒ τ) • ΔType (σ ⇒ τ) • Γ₁
        Γ₂′ = σ • (σ ⇒ τ) • ΔType (σ ⇒ τ) • Γ₂
        ρ₂′ : ⟦ Γ₂′ ⟧Context
        ρ₂′ = v • f • df • ρ
        Γ₁′≼Γ₂′ : Γ₁′ ≼ Γ₂′
        Γ₁′≼Γ₂′ = keep _ • keep _ • keep _ • Γ₁≼Γ₂
        ρ₁′ : ⟦ Γ₁′ ⟧Context
        ρ₁′ = ⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′
        explain : ρ₁′ ≡ v • f • df • (⟦ Γ₁≼Γ₂ ⟧≼ ρ)
        explain = refl
      in
      begin
        ⟦ apply-term {σ ⇒ τ} ⟧Term ρ df f v
      ≡⟨⟩
        ⟦ apply-term {τ} ⟧Term ρ₂′
          (df v (⟦ nil-term {σ} ⟧Term ρ₂′ v)) (f v)
      ≡⟨ cong₂ (λ h1 h2 → h1 (df v (h2 v)) (f v)) (meaning-⊕-invariant {τ} Γ₁′≼Γ₂′ ρ₂′) (meaning-onil-invariant {σ} Γ₁′≼Γ₂′ ρ₂′) ⟩
        ⟦ apply-term {τ} ⟧Term (⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′)
          (df v (⟦ nil-term {σ} ⟧Term (⟦ Γ₁′≼Γ₂′ ⟧≼ ρ₂′) v)) (f v)
      ≡⟨⟩
        ⟦ apply-term {τ} ⟧Term ρ₁′
          (df v (⟦ nil-term {σ} ⟧Term ρ₁′ v)) (f v)
      ≡⟨⟩
        ⟦ apply-term {σ ⇒ τ} ⟧Term (⟦ Γ₁≼Γ₂ ⟧≼ ρ) df f v
      ∎)
    where
      open ≡-Reasoning

  meaning-⊝ {base ι} {Γ} {s} {t} {ρ} = meaning-⊝-base ι {Γ} {s} {t} {ρ}
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

  meaning-onil {base ι} {Γ} {t} {ρ} = meaning-onil-base ι {Γ} {t} {ρ}
  meaning-onil {σ ⇒ τ} {Γ} {t} {ρ} = meaning-⊝ {σ ⇒ τ} {Γ} {t} {t} {ρ}
