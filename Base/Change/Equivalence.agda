------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Delta-observational equivalence
------------------------------------------------------------------------
module Base.Change.Equivalence where

open import Relation.Binary.PropositionalEquality
open import Base.Change.Algebra
open import Level
open import Data.Unit

module _ {a ℓ} {A : Set a} {{ca : ChangeAlgebra ℓ A}} {x : A} where
  -- Delta-observational equivalence: these asserts that two changes
  -- give the same result when applied to a base value.
  _≙_ : ∀ dx dy → Set a
  dx ≙ dy = x ⊞ dx ≡ x ⊞ dy

  -- _≙_ is indeed an equivalence relation:
  ≙-refl : ∀ {dx} → dx ≙ dx
  ≙-refl = refl

  ≙-symm : ∀ {dx dy} → dx ≙ dy → dy ≙ dx
  ≙-symm ≙ = sym ≙

  ≙-trans : ∀ {dx dy dz} → dx ≙ dy → dy ≙ dz → dx ≙ dz
  ≙-trans ≙₁ ≙₂ = trans ≙₁ ≙₂

  -- TODO: we want to show that all functions of interest respect
  -- delta-observational equivalence, so that two d.o.e. changes can be
  -- substituted for each other freely.
  --
  -- * That should be be true for
  --   functions using changes parametrically.
  --
  -- * Moreover, d.o.e. should be respected by contexts [ ] x dx and df x [ ];
  --   this is proved below on both contexts at once by fun-change-respects.
  --
  -- * Finally, change algebra operations should respect d.o.e. But ⊞ respects
  --   it by definition, and ⊟ doesn't take change arguments - we will only
  --   need a proof for compose, when we define it.
  --
  -- Stating the general result, though, seems hard, we should
  -- rather have lemmas proving that certain classes of functions respect this
  -- equivalence.

module _ {a} {b} {c} {d} {A : Set a} {B : Set b}
  {{CA : ChangeAlgebra c A}} {{CB : ChangeAlgebra d B}} where

  module FC = FunctionChanges A B {{CA}} {{CB}}
  open FC using (changeAlgebra; incrementalization)
  open FC.FunctionChange

  fun-change-respects : ∀ {x : A} {dx₁ dx₂ : Δ x} {f : A → B} {df₁ df₂} →
    df₁ ≙ df₂ → dx₁ ≙ dx₂ → apply df₁ x dx₁ ≙ apply df₂ x dx₂
  fun-change-respects {x} {dx₁} {dx₂} {f} {df₁} {df₂} df₁≙df₂ dx₁≙dx₂ = lemma
    where
      open ≡-Reasoning
      -- This type signature just expands the goal manually a bit.
      lemma : f x ⊞ apply df₁ x dx₁ ≡ f x ⊞ apply df₂ x dx₂
      -- Informally: use incrementalization on both sides and then apply
      -- congruence.
      lemma =
        begin
          f x ⊞ apply df₁ x dx₁
        ≡⟨ sym (incrementalization f df₁ x dx₁) ⟩
          (f ⊞ df₁) (x ⊞ dx₁)
        ≡⟨ cong (f ⊞ df₁) dx₁≙dx₂ ⟩
          (f ⊞ df₁) (x ⊞ dx₂)
        ≡⟨ cong (λ f → f (x ⊞ dx₂)) df₁≙df₂ ⟩
          (f ⊞ df₂) (x ⊞ dx₂)
        ≡⟨ incrementalization f df₂ x dx₂ ⟩
          f x ⊞ apply df₂ x dx₂
        ∎

  -- An extensionality principle for delta-observational equivalence: if
  -- applying two function changes to the same base value and input change gives
  -- a d.o.e. result, then the two function changes are d.o.e. themselves.

  delta-ext : ∀ {f : A → B} → ∀ {df dg : Δ f} → (∀ x dx → apply df x dx ≙ apply dg x dx) → df ≙ dg
  delta-ext {f} {df} {dg} dfxdx≙dgxdx = lemma₂
    where
      open ≡-Reasoning
      open import Postulate.Extensionality
      -- This type signature just expands the goal manually a bit.
      lemma₁ : ∀ x dx → f x ⊞ apply df x dx ≡ f x ⊞ apply dg x dx
      lemma₁ = dfxdx≙dgxdx
      lemma₂ : f ⊞ df ≡ f ⊞ dg
      lemma₂ = ext (λ x → lemma₁ x (nil x))