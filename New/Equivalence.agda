module New.Equivalence where

open import Function
open import Relation.Binary

open import New.Changes

module _ {a} {A : Set a} {{CA : ChAlg A}} {x : A} where
  -- Delta-observational equivalence: these asserts that two changes
  -- give the same result when applied to a base value.

  -- To avoid unification problems, use a one-field record (a Haskell "newtype")
  -- instead of a "type synonym".
  record _≙_ (dx dy : Ch A) : Set a where
    -- doe = Delta-Observational Equivalence.
    constructor doe
    field
      proof : x ⊕ dx ≡ x ⊕ dy

  open _≙_ public

  -- Same priority as ≡
  infix 4 _≙_

  -- _≙_ is indeed an equivalence relation:
  ≙-refl : ∀ {dx} → dx ≙ dx
  ≙-refl = doe refl

  ≙-sym : ∀ {dx dy} → dx ≙ dy → dy ≙ dx
  ≙-sym ≙ = doe $ sym $ proof ≙

  ≙-trans : ∀ {dx dy dz} → dx ≙ dy → dy ≙ dz → dx ≙ dz
  ≙-trans ≙₁ ≙₂ = doe $ trans (proof ≙₁) (proof ≙₂)

  -- That's standard congruence applied to ≙
  ≙-cong  : ∀ {b} {B : Set b}
       (f : A → B) {dx dy} → dx ≙ dy → f (x ⊕ dx) ≡ f (x ⊕ dy)
  ≙-cong f da≙db = cong f $ proof da≙db

  ≙-isEquivalence : IsEquivalence (_≙_)
  ≙-isEquivalence = record
    { refl  = ≙-refl
    ; sym   = ≙-sym
    ; trans = ≙-trans
    }

  ≙-setoid : Setoid a a
  ≙-setoid = record
    { Carrier       = Ch A
    ; _≈_           = _≙_
    ; isEquivalence = ≙-isEquivalence
    }

≙-syntax : ∀ {a} {A : Set a} {{CA : ChAlg A}} (x : A) (dx₁ dx₂ : Ch A) → Set a
≙-syntax x dx₁ dx₂ = _≙_ {x = x} dx₁ dx₂
syntax ≙-syntax x dx₁ dx₂ = dx₁ ≙[ x ] dx₂
