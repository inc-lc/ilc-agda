module Base.Change.PointwiseFunctionChanges where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality
open import Level

open import Base.Ascription
open import Base.HetEqExtra
open import Base.Change.Algebra

-- Define an alternative change structure on functions based on pointwise changes. Both functions and changes carry a derivative with them.

module AltFunctionChanges ℓ (A B : Set ℓ) {{CA : ChangeAlgebra ℓ A}} {{CB : ChangeAlgebra ℓ B}} where
  open FunctionChanges A B {{CA}} {{CB}} using (Derivative)

  RawChangeP : (f : A → B) → Set ℓ
  RawChangeP f = (a : A) → Δ (f a)

  FunBaseT : Set ℓ
  FunBaseT = Σ[ f ∈ (A → B) ] Derivative f

  _raw⊕_ : (f : A → B) → (df : RawChangeP f) → (A → B)
  f raw⊕ df = λ a → f a ⊞ df a

  _raw⊝_ : (g f : A → B) → RawChangeP f
  g raw⊝ f = λ a → g a ⊟ f a

  rawnil : (f : A → B) → RawChangeP f
  rawnil f = λ a → nil (f a)

  raw-update-nil : ∀ f → f raw⊕ (rawnil f) ≡ f
  raw-update-nil f = ext (λ a → update-nil (f a))
  raw-update-diff : ∀ f g → f raw⊕ (g raw⊝ f) ≡ g
  raw-update-diff f g = ext (λ a → update-diff (g a) (f a))

  Derivative-f⊕df : ∀ (f : A → B) (df : RawChangeP f) → Derivative (f raw⊕ df)
  Derivative-f⊕df f df
    = ( (λ a da → f (a ⊞ da) ⊞ df (a ⊞ da) ⊟ (f a ⊞ df a))
      , (λ a da → update-diff (f (a ⊞ da) ⊞ df (a ⊞ da)) (f a ⊞ df a))
      )
  -- Instead of ` f (a ⊞ da) ` we could/should use` f a ⊞ f′ a da `,
  -- but we'd need to invoke the right equivalence for the expression to typecheck.
  -- XXX: that derivative is very non-incremental.
  -- Alternatives:
  -- 1. (invert df x) andThen (f' x dx) andThen (df (x ⊞ dx))
  -- 2. include a derivative in the function change as well. That would limit the point though.

  FChange₀ : (A → B) → Set ℓ
  FChange₀ f₀ = Σ[ df ∈ RawChangeP f₀ ] Derivative (f₀ raw⊕ df)

  FChange : FunBaseT → Set ℓ
  FChange (f₀ , _f₀′) = FChange₀ f₀

  _⊕_ : (f : FunBaseT) → FChange f → FunBaseT
  (f₀ , _f₀′) ⊕ (df , f₁′) = (f₀ raw⊕ df , f₁′)

  -- Lemmas to transport across the f₁ᵇ ≅ f₁ᵃ equality.
  transport-derivative-to-equiv-base : ∀ {f₁ᵃ f₁ᵇ} (eq : f₁ᵇ ≡ f₁ᵃ) → Derivative f₁ᵃ → Derivative f₁ᵇ
  transport-derivative-to-equiv-base refl f₁′ = f₁′

  transport-base-f : ∀ {f₀ f₁} df → Derivative f₁ → (f₀ raw⊕ df ≡ f₁) → FChange₀ f₀
  transport-base-f df f₁′ eq = df , transport-derivative-to-equiv-base eq f₁′
  -- Implementation note: transport-base-f can't pattern match on eq because of a unification failure.
  -- Hence we called the generalized transport-derivative-to-equiv-base, where the problem disappears.

  transport-base-f-eq : ∀ {f₁ᵃ f₁ᵇ} (eq : f₁ᵇ ≡ f₁ᵃ) (f₁′ : Derivative f₁ᵃ) →
    (f₁ᵇ , transport-derivative-to-equiv-base eq f₁′) ≡ (f₁ᵃ , f₁′)
  transport-base-f-eq refl f₁′ = refl

  f-nil : (f : FunBaseT) → FChange f
  f-nil (f , f′) = transport-base-f (rawnil f) f′ (raw-update-nil f)

  f-update-nil : ∀ fstr → (fstr ⊕ f-nil fstr) ≡ fstr
  f-update-nil (f , f′) = transport-base-f-eq (raw-update-nil f) f′

  _⊝_ : (g f : FunBaseT) → FChange f
  _⊝_ (g , g′) (f , _f′) = transport-base-f (g raw⊝ f) g′ (raw-update-diff f g)

  f-update-diff : ∀ gstr fstr → fstr ⊕ (gstr ⊝ fstr) ≡ gstr
  f-update-diff (g , g′) (f , _f′) = transport-base-f-eq (raw-update-diff f g) g′

  changeAlgebra : ChangeAlgebra ℓ FunBaseT
  changeAlgebra = record
                    { Change = FChange
                    ; update = _⊕_
                    ; diff = _⊝_
                    ; nil = f-nil
                    ; isChangeAlgebra = record { update-diff = f-update-diff ; update-nil = f-update-nil }
                    }
