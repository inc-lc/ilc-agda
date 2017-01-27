module Base.Change.Sums where

open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Level

open import Base.Ascription
open import Base.Change.Algebra
open import Base.Change.Equivalence
open import Base.Change.Equivalence.Realizers
open import Postulate.Extensionality

module SumChanges ℓ {X Y : Set ℓ} {{CX : ChangeAlgebra X}} {{CY : ChangeAlgebra Y}} where
  open ≡-Reasoning

  -- This is an indexed datatype, so it has two constructors per argument. But
  -- erasure would probably not be smart enough to notice.

  -- Should we rewrite this as two separate datatypes?
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

  instance
    changeAlgebraSums : ChangeAlgebra (X ⊎ Y)
    changeAlgebraSums = record
      { Change = SumChange
      ; update = _⊕_
      ; diff = _⊝_
      ; nil = s-nil
      ; isChangeAlgebra = record
        { update-diff = s-update-diff
        ; update-nil = s-update-nil
        }
      }

  inj₁′ : Δ (inj₁ as (X → (X ⊎ Y)))
  inj₁′ = nil inj₁

  inj₁′-realizer : RawChange (inj₁ as (X → (X ⊎ Y)))
  inj₁′-realizer x dx = ch₁ dx

  inj₁′Derivative : IsDerivative (inj₁ as (X → (X ⊎ Y))) inj₁′-realizer
  inj₁′Derivative x dx = refl

  inj₁′-realizer-correct : ∀ a da → apply inj₁′ a da ≙₍ inj₁ a as (X ⊎ Y) ₎ inj₁′-realizer a da
  inj₁′-realizer-correct a da = diff-update

  inj₁′-faster-w-proof : equiv-raw-change-to-change-ResType inj₁ inj₁′-realizer
  inj₁′-faster-w-proof = equiv-raw-change-to-change inj₁ inj₁′ inj₁′-realizer inj₁′-realizer-correct
  inj₁′-faster : Δ inj₁
  inj₁′-faster = proj₁ inj₁′-faster-w-proof

  inj₂′ : Δ (inj₂ as (Y → (X ⊎ Y)))
  inj₂′ = nil inj₂

  inj₂′-realizer : RawChange (inj₂ as (Y → (X ⊎ Y)))
  inj₂′-realizer y dy = ch₂ dy

  inj₂′Derivative : IsDerivative (inj₂ as (Y → (X ⊎ Y))) inj₂′-realizer
  inj₂′Derivative y dy = refl

  inj₂′-realizer-correct : ∀ b db → apply inj₂′ b db ≙₍ inj₂ b as (X ⊎ Y) ₎ inj₂′-realizer b db
  inj₂′-realizer-correct b db = diff-update

  inj₂′-faster-w-proof : equiv-raw-change-to-change-ResType inj₂ inj₂′-realizer
  inj₂′-faster-w-proof = equiv-raw-change-to-change inj₂ inj₂′ inj₂′-realizer inj₂′-realizer-correct
  inj₂′-faster : Δ inj₂
  inj₂′-faster = proj₁ inj₂′-faster-w-proof

  module _ {Z : Set ℓ} {{CZ : ChangeAlgebra Z}} where
    -- Elimination form for sums. This is a less dependently-typed version of
    -- [_,_].
    match : (X → Z) → (Y → Z) → X ⊎ Y → Z
    match f g (inj₁ x) = f x
    match f g (inj₂ y) = g y

    match′ : Δ match
    match′ = nil match

    match′-realizer : (f : X → Z) → Δ f → (g : Y → Z) → Δ g → (s : X ⊎ Y) → Δ s → Δ (match f g s)
    match′-realizer f df g dg (inj₁ x) (ch₁ dx) = apply df x dx
    match′-realizer f df g dg (inj₁ x) (rp₁₂ y) = ((g ⊞ dg) y) ⊟ (f x)
    match′-realizer f df g dg (inj₂ y) (rp₂₁ x) = ((f ⊞ df) x) ⊟ (g y)
    match′-realizer f df g dg (inj₂ y) (ch₂ dy) = apply dg y dy

    match′-realizer-correct :
      (f : X → Z) → (df : Δ f) → (g : Y → Z) → (dg : Δ g) → (s : X ⊎ Y) → (ds : Δ s) →
      apply (apply (apply match′ f df) g dg) s ds ≙₍ match f g s ₎ match′-realizer f df g dg s ds
    match′-realizer-correct f df g dg (inj₁ x) (ch₁ dx) = ≙-incrementalization f df x dx
    match′-realizer-correct f df g dg (inj₁ x) (rp₁₂ y) = ≙-refl
    match′-realizer-correct f df g dg (inj₂ y) (ch₂ dy) = ≙-incrementalization g dg y dy
    match′-realizer-correct f df g dg (inj₂ y) (rp₂₁ x) = ≙-refl

    -- We need a ternary variant of the lemma here.
    match′-faster-w-proof : equiv-raw-change-to-change-ternary-ResType match match′-realizer
    match′-faster-w-proof = equiv-raw-change-to-change-ternary match match′ match′-realizer match′-realizer-correct

    match′-faster : Δ match
    match′-faster = proj₁ match′-faster-w-proof
