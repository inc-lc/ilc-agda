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
open import Function

open import Base.Change.Equivalence.Base public
open import Base.Change.Equivalence.EqReasoning public

module _ {a ℓ} {A : Set a} {{ca : ChangeAlgebra ℓ A}} {x : A} where
  -- By update-nil, if dx = nil x, then x ⊞ dx ≡ x.
  -- As a consequence, if dx ≙ nil x, then x ⊞ dx ≡ x
  nil-is-⊞-unit : ∀ (dx : Δ {{ca}} x) → dx ≙ nil x → x ⊞ dx ≡ x
  nil-is-⊞-unit dx dx≙nil-x =
    begin
      x ⊞ dx
    ≡⟨ proof dx≙nil-x ⟩
      x ⊞ (nil {{ca}} x)
    ≡⟨ update-nil {{ca}} x ⟩
      x
    ∎
    where
      open ≡-Reasoning

  -- Here we prove the inverse:
  ⊞-unit-is-nil : ∀ (dx : Δ {{ca}} x) → x ⊞ dx ≡ x → _≙_ {{ca}} dx (nil {{ca}} x)
  ⊞-unit-is-nil dx x⊞dx≡x = doe $
    begin
      x ⊞ dx
    ≡⟨ x⊞dx≡x ⟩
      x
    ≡⟨ sym (update-nil {{ca}} x) ⟩
      x ⊞ nil {{ca}} x
    ∎
    where
      open ≡-Reasoning

  -- Let's show that nil x is d.o.e. to x ⊟ x
  nil-x-is-x⊟x : nil x ≙ x ⊟ x
  nil-x-is-x⊟x = ≙-sym (⊞-unit-is-nil (x ⊟ x) (update-diff {{ca}} x x))

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

  -- This results pairs with update-diff.
  diff-update : ∀ {dx : Δ {{ca}} x} → (x ⊞ dx) ⊟ x ≙ dx
  diff-update {dx} = doe lemma
    where
      lemma : _⊞_ {{ca}} x (x ⊞ dx ⊟ x) ≡ x ⊞ dx
      lemma = update-diff {{ca}} (x ⊞ dx) x

module _ {a} {b} {c} {d} {A : Set a} {B : Set b}
  {{CA : ChangeAlgebra c A}} {{CB : ChangeAlgebra d B}} where

  module FC = FunctionChanges A B {{CA}} {{CB}}
  open FC using (changeAlgebra; incrementalization; DerivativeAsChange)
  open FC.FunctionChange

  fun-change-respects : ∀ {x : A} {dx₁ dx₂ : Δ x} {f : A → B} {df₁ df₂} →
    _≙_ {{changeAlgebra}} df₁ df₂ → dx₁ ≙ dx₂ → apply df₁ x dx₁ ≙ apply df₂ x dx₂
  fun-change-respects {x} {dx₁} {dx₂} {f} {df₁} {df₂} df₁≙df₂ dx₁≙dx₂ = doe lemma
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
        ≡⟨ ≙-cong (f ⊞ df₁) dx₁≙dx₂ ⟩
          (f ⊞ df₁) (x ⊞ dx₂)
        ≡⟨ ≙-cong (λ f → f (x ⊞ dx₂)) df₁≙df₂ ⟩
          (f ⊞ df₂) (x ⊞ dx₂)
        ≡⟨ incrementalization f df₂ x dx₂ ⟩
          f x ⊞ apply df₂ x dx₂
        ∎

  open import Postulate.Extensionality

  -- An extensionality principle for delta-observational equivalence: if
  -- applying two function changes to the same base value and input change gives
  -- a d.o.e. result, then the two function changes are d.o.e. themselves.

  delta-ext : ∀ {f : A → B} → ∀ {df dg : Δ f} → (∀ x dx → apply df x dx ≙ apply dg x dx) → df ≙ dg
  delta-ext {f} {df} {dg} df-x-dx≙dg-x-dx = doe lemma₂
    where
      open ≡-Reasoning
      -- This type signature just expands the goal manually a bit.
      lemma₁ : ∀ x dx → f x ⊞ apply df x dx ≡ f x ⊞ apply dg x dx
      lemma₁ x dx = proof $ df-x-dx≙dg-x-dx x dx
      lemma₂ : f ⊞ df ≡ f ⊞ dg
      lemma₂ = ext (λ x → lemma₁ x (nil x))

  -- You could think that the function should relate equivalent changes, but
  -- that's a stronger hypothesis, which doesn't give you extra guarantees. But
  -- here's the statement and proof, for completeness:

  delta-ext₂ : ∀ {f : A → B} → ∀ {df dg : Δ f} → (∀ x dx₁ dx₂ → _≙_ {{CA}} dx₁ dx₂ → apply df x dx₁ ≙ apply dg x dx₂) → df ≙ dg
  delta-ext₂ {f} {df} {dg} df-x-dx≙dg-x-dx = delta-ext (λ x dx → df-x-dx≙dg-x-dx x dx dx ≙-refl)

  -- We know that Derivative f (apply (nil f)) (by nil-is-derivative).
  -- That is, df = nil f -> Derivative f (apply df).
  -- Now, we try to prove that if Derivative f (apply df) -> df = nil f.
  -- But first, we prove that f ⊞ df = f.
  derivative-is-⊞-unit : ∀ {f : A → B} df →
    Derivative f (apply df) → f ⊞ df ≡ f
  derivative-is-⊞-unit {f} df fdf =
    begin
      f ⊞ df
    ≡⟨⟩
      (λ x → f x ⊞ apply df x (nil x))
    ≡⟨ ext (λ x → fdf x (nil x)) ⟩
      (λ x → f (x ⊞ nil {{CA}} x))
    ≡⟨ ext (λ x → cong f (update-nil {{CA}} x)) ⟩
      (λ x → f x)
    ≡⟨⟩
      f
    ∎
    where
      open ≡-Reasoning

  -- We can restate the above as "df is a nil change".

  derivative-is-nil : ∀ {f : A → B} df →
    Derivative f (apply df) → df ≙ nil f
  derivative-is-nil df fdf = ⊞-unit-is-nil df (derivative-is-⊞-unit df fdf)

  derivative-is-nil-alternative : ∀ {f : A → B} df →
    (Derivative-f-df : Derivative f df) → DerivativeAsChange df Derivative-f-df ≙ nil f
  derivative-is-nil-alternative df Derivative-f-df = derivative-is-nil (DerivativeAsChange df Derivative-f-df) Derivative-f-df

  -- If we have two derivatives, they're both nil, hence they're equal.
  derivative-unique : ∀ {f : A → B} {df dg : Δ f} → Derivative f (apply df) → Derivative f (apply dg) → df ≙ dg
  derivative-unique {f} {df} {dg} fdf fdg =
    begin
      df
    ≙⟨ derivative-is-nil df fdf ⟩
      nil f
    ≙⟨ ≙-sym (derivative-is-nil dg fdg) ⟩
      dg
    ∎
    where
      open ≙-Reasoning

  -- This is Lemma 2.5 in the paper. Note that the statement in the paper uses
  -- (incorrectly) normal equality instead of delta-observational equivalence.
  deriv-zero :
    (f : A → B) → (df : (a : A) (da : Δ a) → Δ (f a)) → Derivative f df →
    ∀ v → df v (nil {{CA}} v) ≙ nil {{CB}} (f v)
  deriv-zero f df proof v = doe lemma
    where
      open ≡-Reasoning
      lemma : f v ⊞ df v (nil v) ≡ f v ⊞ nil {{CB}} (f v)
      lemma =
        begin
          f v ⊞ df v (nil {{CA}} v)
        ≡⟨ proof v (nil {{CA}} v) ⟩
          f (v ⊞ (nil {{CA}} v))
        ≡⟨ cong f (update-nil {{CA}} v) ⟩
          f v
        ≡⟨ sym (update-nil {{CB}} (f v)) ⟩
          f v ⊞ nil {{CB}} (f v)
        ∎
