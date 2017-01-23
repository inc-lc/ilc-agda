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

module _ {a} {A : Set a} {{ca : ChangeAlgebra A}} {x : A} where
  -- By update-nil, if dx = nil x, then x ⊞ dx ≡ x.
  -- As a consequence, if dx ≙ nil x, then x ⊞ dx ≡ x
  nil-is-⊞-unit : ∀ (dx : Δ x) → dx ≙ nil x → x ⊞ dx ≡ x
  nil-is-⊞-unit dx dx≙nil-x =
    begin
      x ⊞ dx
    ≡⟨ proof dx≙nil-x ⟩
      x ⊞ (nil x)
    ≡⟨ update-nil x ⟩
      x
    ∎
    where
      open ≡-Reasoning

  -- Here we prove the inverse:
  ⊞-unit-is-nil : ∀ (dx : Δ x) → x ⊞ dx ≡ x → dx ≙ (nil x)
  ⊞-unit-is-nil dx x⊞dx≡x = doe $
    begin
      x ⊞ dx
    ≡⟨ x⊞dx≡x ⟩
      x
    ≡⟨ sym (update-nil x) ⟩
      x ⊞ nil x
    ∎
    where
      open ≡-Reasoning

  -- Let's show that nil x is d.o.e. to x ⊟ x
  nil-x-is-x⊟x : nil x ≙ x ⊟ x
  nil-x-is-x⊟x = ≙-sym (⊞-unit-is-nil (x ⊟ x) (update-diff x x))

  -- TODO: we want to show that all functions of interest respect
  -- delta-observational equivalence, so that two d.o.e. changes can be
  -- substituted for each other freely.
  --
  -- * That should be be true for
  --   functions using changes parametrically.
  --
  -- * Moreover, d.o.e. should be respected by contexts [ ] x dx and df x [ ];
  --   this is proved below on both contexts at once by
  --   equiv-fun-changes-respect, and its corollaries fun-change-respects and
  --   equiv-fun-changes-funs.
  --
  -- * Finally, change algebra operations should respect d.o.e. But ⊞ respects
  --   it by definition, and ⊟ doesn't take change arguments - we will only
  --   need a proof for compose, when we define it.
  --
  -- Stating the general result, though, seems hard, we should
  -- rather have lemmas proving that certain classes of functions respect this
  -- equivalence.

  -- This results pairs with update-diff.
  diff-update : ∀ {dx : Δ x} → (x ⊞ dx) ⊟ x ≙ dx
  diff-update {dx} = doe lemma
    where
      lemma : x ⊞ (x ⊞ dx ⊟ x) ≡ x ⊞ dx
      lemma = update-diff (x ⊞ dx) x

  -- \begin{lemma}[Equivalence cancellation]
  --   |v2 `ominus` v1 `doe` dv| holds if and only if |v2 = v1 `oplus`
  --   dv|, for any |v1, v2 `elem` V| and |dv `elem` Dt ^ v1|.
  -- \end{lemma}

  equiv-cancel-1 : ∀ x' dx → (x' ⊟ x) ≙ dx → x' ≡ x ⊞ dx
  equiv-cancel-1 x' dx (doe x'⊟x≙dx) = trans (sym (update-diff x' x)) x'⊟x≙dx
  equiv-cancel-2 : ∀ x' dx → x' ≡ x ⊞ dx → x' ⊟ x ≙ dx
  equiv-cancel-2 _ dx refl = diff-update

module _ {a} {b} {A : Set a} {B : Set b}
  {{CA : ChangeAlgebra A}} {{CB : ChangeAlgebra B}} where

  module FC = FunctionChanges A B
  open FC using (changeAlgebra; incrementalization; DerivativeAsChange)
  open FC.FunctionChange

  equiv-fun-changes-respect : ∀ {x : A} {dx₁ dx₂ : Δ x} {f : A → B} {df₁ df₂ : Δ f} →
    _≙_ {x = f} df₁ df₂ → dx₁ ≙ dx₂ → apply df₁ x dx₁ ≙ apply df₂ x dx₂
  equiv-fun-changes-respect {x} {dx₁} {dx₂} {f} {df₁} {df₂} df₁≙df₂ dx₁≙dx₂ = doe lemma
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

  fun-change-respects : ∀ {x : A} {dx₁ dx₂} {f : A → B} (df : Δ f) →
    dx₁ ≙ dx₂ → apply df x dx₁ ≙ apply df x dx₂
  fun-change-respects df dx₁≙dx₂ = equiv-fun-changes-respect (≙-refl {dx = df}) dx₁≙dx₂

  -- D.o.e. function changes behave like the same function (up to d.o.e.).
  equiv-fun-changes-funs : ∀ {x : A} {dx} {f : A → B} {df₁ df₂} →
    _≙_ {x = f} df₁ df₂ → apply df₁ x dx ≙ apply df₂ x dx
  equiv-fun-changes-funs {dx = dx} df₁≙df₂ = equiv-fun-changes-respect df₁≙df₂ (≙-refl {dx = dx})

  derivative-doe-characterization : ∀ {a : A} {da : Δ a}
    {f : A → B} {df : RawChange f} (is-derivative : IsDerivative f df) →
    df a da ≙ f (a ⊞ da) ⊟ f a
  derivative-doe-characterization {a} {da} {f} {df} is-derivative = doe lemma
    where
      open ≡-Reasoning
      lemma : f a ⊞ df a da ≡ f a ⊞ (f (a ⊞ da) ⊟ f a)
      lemma =
        begin
          (f a ⊞ df a da)
        ≡⟨ is-derivative a da ⟩
          (f (a ⊞ da))
        ≡⟨ sym (update-diff (f (a ⊞ da)) (f a)) ⟩
          (f a ⊞ (f (a ⊞ da) ⊟ f a))
        ∎

  derivative-respects-doe : ∀ {x : A} {dx₁ dx₂ : Δ x}
    {f : A → B} {df : RawChange f} (is-derivative : IsDerivative f df) →
    dx₁ ≙ dx₂ → df x dx₁ ≙ df x dx₂
  derivative-respects-doe {x} {dx₁} {dx₂} {f} {df} is-derivative dx₁≙dx₂ =
    begin
      df x dx₁
    ≙⟨ derivative-doe-characterization is-derivative ⟩
      f (x ⊞ dx₁) ⊟ f x
    ≡⟨ cong (λ v → f v  ⊟ f x) (proof dx₁≙dx₂) ⟩
      f (x ⊞ dx₂) ⊟ f x
    ≙⟨ ≙-sym (derivative-doe-characterization is-derivative) ⟩
      df x dx₂
    ∎
    where
      open ≙-Reasoning

  -- This is also a corollary of fun-changes-respect
  derivative-respects-doe-alt : ∀ {x : A} {dx₁ dx₂ : Δ x}
    {f : A → B} {df : RawChange f} (is-derivative : IsDerivative f df) →
    dx₁ ≙ dx₂ → df x dx₁ ≙ df x dx₂
  derivative-respects-doe-alt {x} {dx₁} {dx₂} {f} {df} is-derivative dx₁≙dx₂ =
    fun-change-respects (DerivativeAsChange is-derivative) dx₁≙dx₂

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

  delta-ext₂ : ∀ {f : A → B} → ∀ {df dg : Δ f} → (∀ x (dx₁ dx₂ : Δ x) → _≙_ {x = x} dx₁ dx₂ → apply df x dx₁ ≙ apply dg x dx₂) → df ≙ dg
  delta-ext₂ {f} {df} {dg} df-x-dx≙dg-x-dx = delta-ext (λ x dx → df-x-dx≙dg-x-dx x dx dx ≙-refl)

  -- We know that IsDerivative f (apply (nil f)) (by nil-is-derivative).
  -- That is, df = nil f -> IsDerivative f (apply df).
  -- Now, we try to prove that if IsDerivative f (apply df) -> df = nil f.
  -- But first, we prove that f ⊞ df = f.
  derivative-is-⊞-unit : ∀ {f : A → B} df →
    IsDerivative f (apply df) → f ⊞ df ≡ f
  derivative-is-⊞-unit {f} df fdf =
    begin
      f ⊞ df
    ≡⟨⟩
      (λ x → f x ⊞ apply df x (nil x))
    ≡⟨ ext (λ x → fdf x (nil x)) ⟩
      (λ x → f (x ⊞ nil x))
    ≡⟨ ext (λ x → cong f (update-nil x)) ⟩
      (λ x → f x)
    ≡⟨⟩
      f
    ∎
    where
      open ≡-Reasoning

  -- We can restate the above as "df is a nil change".

  derivative-is-nil : ∀ {f : A → B} df →
    IsDerivative f (apply df) → df ≙ nil f
  derivative-is-nil df fdf = ⊞-unit-is-nil df (derivative-is-⊞-unit df fdf)

  derivative-is-nil-alternative : ∀ {f : A → B} df →
    (IsDerivative-f-df : IsDerivative f df) → DerivativeAsChange IsDerivative-f-df ≙ nil f
  derivative-is-nil-alternative df IsDerivative-f-df = derivative-is-nil (DerivativeAsChange IsDerivative-f-df) IsDerivative-f-df

  nil-is-derivative : ∀ (f : A → B) → IsDerivative f (apply (nil f))
  nil-is-derivative f a da =
    begin
      f a ⊞ apply (nil f) a da
    ≡⟨ sym (incrementalization f (nil f) a da) ⟩
      (f ⊞ nil f) (a ⊞ da)
    ≡⟨ cong (λ □ → □ (a ⊞ da)) (update-nil f) ⟩
      f (a ⊞ da)
    ∎
    where
      open ≡-Reasoning

  -- If we have two derivatives, they're both nil, hence they're equivalent.
  derivative-unique : ∀ {f : A → B} {df dg : Δ f} → IsDerivative f (apply df) → IsDerivative f (apply dg) → df ≙ dg
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

  equiv-derivative-is-derivative : ∀ {f : A → B} df₁ df₂ → IsDerivative f (apply df₁) →  _≙_ {x = f} df₁ df₂ → IsDerivative f (apply df₂)
  equiv-derivative-is-derivative {f} df₁ df₂ IsDerivative-f-df₁ df₁≙df₂ a da =
    begin
      f a ⊞ apply df₂ a da
    ≡⟨ sym (incrementalization f df₂ a da) ⟩
      (f ⊞ df₂) (a ⊞ da)
    ≡⟨ cong (λ □ → □ (a ⊞ da)) lemma ⟩
      f (a ⊞ da)
    ∎
    where
      open ≡-Reasoning
      lemma : f ⊞ df₂ ≡ f
      lemma =
        begin
          f ⊞ df₂
        ≡⟨ proof (≙-sym df₁≙df₂) ⟩
          f ⊞ df₁
        ≡⟨ derivative-is-⊞-unit df₁ IsDerivative-f-df₁ ⟩
          f
        ∎

  -- This is Lemma 2.5 in the paper. Note that the statement in the paper uses
  -- (incorrectly) normal equality instead of delta-observational equivalence.
  deriv-zero :
    ∀ (f : A → B) df → IsDerivative f df →
    ∀ v → df v (nil v) ≙ nil (f v)
  deriv-zero f df proof v = doe lemma
    where
      open ≡-Reasoning
      lemma : f v ⊞ df v (nil v) ≡ f v ⊞ nil (f v)
      lemma =
        begin
          f v ⊞ df v (nil v)
        ≡⟨ proof v (nil v) ⟩
          f (v ⊞ (nil v))
        ≡⟨ cong f (update-nil v) ⟩
          f v
        ≡⟨ sym (update-nil (f v)) ⟩
          f v ⊞ nil (f v)
        ∎
