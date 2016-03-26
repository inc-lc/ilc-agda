module Base.Change.Sums where

open import Relation.Binary.PropositionalEquality
open import Level

open import Base.Change.Algebra
open import Base.Change.Equivalence
open import Postulate.Extensionality
open import Data.Sum

module SumChanges ℓ (X Y : Set ℓ) {{CX : ChangeAlgebra ℓ X}} {{CY : ChangeAlgebra ℓ Y}} where
  open ≡-Reasoning

  data SumChange : X ⊎ Y → Set ℓ where
    ch₁ : ∀ {x} → (dx : Δ x) → SumChange (inj₁ x)
    rp₁₂ : ∀ {x} → (y : Y) → SumChange (inj₁ x)
    ch₂ : ∀ {y} → (dy : Δ y) → SumChange (inj₂ y)
    rp₂₁ : ∀ {y} → (x : X) → SumChange (inj₂ y)

  _⊕_ : (v : X ⊎ Y) → SumChange v → X ⊎ Y
  inj₁ x ⊕ ch₁ dx = inj₁ (x ⊞ dx)
  inj₂ y ⊕ ch₂ dy = inj₂ (y ⊞ dy)
  inj₁ x ⊕ rp₁₂ y = inj₂ y
  inj₂ y ⊕ rp₂₁ x = inj₁ x

  _⊝_ : ∀ (v₂ v₁ : X ⊎ Y) → SumChange v₁
  inj₁ x₂ ⊝ inj₁ x₁ = ch₁ (x₂ ⊟ x₁)
  inj₂ y₂ ⊝ inj₂ y₁ = ch₂ (y₂ ⊟ y₁)
  inj₂ y₂ ⊝ inj₁ x₁ = rp₁₂ y₂
  inj₁ x₂ ⊝ inj₂ y₁ = rp₂₁ x₂

  s-nil : (v : X ⊎ Y) → SumChange v
  s-nil (inj₁ x) = ch₁ (nil x)
  s-nil (inj₂ y) = ch₂ (nil y)

  s-update-diff : ∀ (u v : X ⊎ Y) → v ⊕ (u ⊝ v) ≡ u
  s-update-diff (inj₁ x₂) (inj₁ x₁) = cong inj₁ (update-diff x₂ x₁)
  s-update-diff (inj₂ y₂) (inj₂ y₁) = cong inj₂ (update-diff y₂ y₁)
  s-update-diff (inj₁ x₂) (inj₂ y₁) = refl
  s-update-diff (inj₂ y₂) (inj₁ x₁) = refl

  s-update-nil : ∀ v → v ⊕ (s-nil v) ≡ v
  s-update-nil (inj₁ x) = cong inj₁ (update-nil x)
  s-update-nil (inj₂ y) = cong inj₂ (update-nil y)

  changeAlgebra : ChangeAlgebra ℓ (X ⊎ Y)
  changeAlgebra = record
    { Change = SumChange
    ; update = _⊕_
    ; diff = _⊝_
    ; nil = s-nil
    ; isChangeAlgebra = record
      { update-diff = s-update-diff
      ; update-nil = s-update-nil
      }
    }

  inj₁′ : (x : X) → (dx : Δ x) → Δ (inj₁ x)
  inj₁′ x dx = ch₁ dx

  inj₁′Derivative : Derivative inj₁ inj₁′
  inj₁′Derivative x dx = refl

  inj₂′ : (y : Y) → (dy : Δ y) → Δ (inj₂ y)
  inj₂′ y dy = ch₂ dy

  inj₂′Derivative : Derivative inj₂ inj₂′
  inj₂′Derivative y dy = refl

  -- Elimination form for sums. This is a less dependently-typed version of
  -- [_,_].
  match : ∀ {Z : Set ℓ} → (X → Z) → (Y → Z) → X ⊎ Y → Z
  match f g (inj₁ x) = f x
  match f g (inj₂ y) = g y

  module _ {Z : Set ℓ} {{CZ : ChangeAlgebra ℓ Z}} where
    X→Z = FunctionChanges.changeAlgebra X Z
    --module ΔX→Z = FunctionChanges X Z {{CX}} {{CZ}}
    Y→Z = FunctionChanges.changeAlgebra Y Z
    --module ΔY→Z = FunctionChanges Y Z {{CY}} {{CZ}}
    X⊎Y→Z = FunctionChanges.changeAlgebra (X ⊎ Y) Z
    Y→Z→X⊎Y→Z = FunctionChanges.changeAlgebra (Y → Z) (X ⊎ Y → Z)

    open FunctionChanges using (apply; correct)

    match′₀-realizer : (f : X → Z) → Δ f → (g : Y → Z) → Δ g → (s : X ⊎ Y) → Δ s → Δ (match f g s)
    match′₀-realizer f df g dg (inj₁ x) (ch₁ dx) = apply df x dx
    match′₀-realizer f df g dg (inj₁ x) (rp₁₂ y) = ((g ⊞ dg) y) ⊟ (f x)
    match′₀-realizer f df g dg (inj₂ y) (rp₂₁ x) = ((f ⊞ df) x) ⊟ (g y)
    match′₀-realizer f df g dg (inj₂ y) (ch₂ dy) = apply dg y dy

    match′₀-realizer-correct : (f : X → Z) → (df : Δ f) → (g : Y → Z) → (dg : Δ g) → (s : X ⊎ Y) → (ds : Δ s) → match f g (s ⊕ ds) ⊞ match′₀-realizer f df g dg (s ⊕ ds) (nil (s ⊕ ds)) ≡ match f g s ⊞ match′₀-realizer f df g dg s ds
    match′₀-realizer-correct f df g dg (inj₁ x) (ch₁ dx) = correct df x dx
    match′₀-realizer-correct f df g dg (inj₂ y) (ch₂ dy) = correct dg y dy
    match′₀-realizer-correct f df g dg (inj₁ x) (rp₁₂ y) rewrite update-diff ((g ⊞ dg) y) (f x) = refl
    match′₀-realizer-correct f df g dg (inj₂ y) (rp₂₁ x) rewrite update-diff ((f ⊞ df) x) (g y) = refl

    match′₀ : (f : X → Z) → Δ f → (g : Y → Z) → Δ g → Δ (match f g)
    match′₀ f df g dg = record { apply = match′₀-realizer f df g dg ; correct = match′₀-realizer-correct f df g dg }

    match′-realizer-correct-body : (f : X → Z) → (df : Δ f) → (g : Y → Z) → (dg : Δ g) → (s : X ⊎ Y) →
      (match f (g ⊞ dg) ⊞ match′₀ f df (g ⊞ dg) (nil (g ⊞ dg))) s ≡ (match f g ⊞ match′₀ f df g dg) s

    match′-realizer-correct-body f df g dg (inj₁ x) = refl
    -- refl doesn't work here. That seems a *huge* bad smell. However, that's simply because we're only updating g, not f
    match′-realizer-correct-body f df g dg (inj₂ y) rewrite update-nil y = update-diff (g y ⊞ apply dg y (nil y)) (g y ⊞ apply dg y (nil y))

    match′-realizer-correct : (f : X → Z) → (df : Δ f) → (g : Y → Z) → (dg : Δ g) →
      (match f (g ⊞ dg)) ⊞ match′₀ f df (g ⊞ dg) (nil (g ⊞ dg)) ≡ match f g ⊞ match′₀ f df g dg
    match′-realizer-correct f df g dg = ext (match′-realizer-correct-body f df g dg)
    match′ : (f : X → Z) → Δ f → Δ (match f)
    match′ f df = record { apply = λ g dg → match′₀ f df g dg ; correct = match′-realizer-correct f df }
