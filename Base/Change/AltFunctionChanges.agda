module Base.Change.AltFunctionChanges where

open import Data.Product
open import Function
import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
open import Postulate.Extensionality
open import Level

open import Base.Ascription
open import Base.HetEqExtra
open import Base.Change.Algebra

-- Define an alternative change structure on functions based on pointwise changes. Both functions and changes carry a derivative with them.

module AltFunctionChanges ℓ (A B : Set ℓ) {{CA : ChangeAlgebra ℓ A}} {{CB : ChangeAlgebra ℓ B}} where
  open ≅-Reasoning

  RawChangeP : (f : A → B) → Set ℓ
  RawChangeP f = (a : A) → Δ (f a)

  FunBaseT : Set ℓ
  FunBaseT = Σ[ f ∈ (A → B) ] Σ[ f′ ∈ RawChange f ] IsDerivative f f′

  _raw⊕_ : (f : A → B) → (df : RawChangeP f) → (A → B)
  f raw⊕ df = λ a → f a ⊞ df a

  _raw⊝_ : (g f : A → B) → RawChangeP f
  g raw⊝ f = λ a → g a ⊟ f a

  rawnil : (f : A → B) → RawChangeP f
  rawnil f = λ a → nil (f a)

  raw-update-nil : ∀ f → f raw⊕ (rawnil f) ≅ f
  raw-update-nil f = hext (λ a → update-nil (f a))
  raw-update-diff : ∀ f g → f raw⊕ (g raw⊝ f) ≅ g
  raw-update-diff f g = hext (λ a → update-diff (g a) (f a))

  deriv-f⊕df : ∀ (f : A → B) (df : RawChangeP f) → RawChange (f raw⊕ df)
  deriv-f⊕df f df = λ a da → f (a ⊞ da) ⊞ df (a ⊞ da) ⊟ (f a ⊞ df a)
  -- Instead of ` f (a ⊞ da) ` we could/should use` f a ⊞ f′ a da `,
  -- but we'd need to invoke the right equivalence for the expression to typecheck.
  -- XXX: that derivative is very non-incremental.
  -- Alternatives:
  -- 1. (invert df x) andThen (f' x dx) andThen (df (x ⊞ dx))
  -- 2. include a derivative in the function change as well. That would limit the point though.

  IsDerivative-deriv-f⊕df : (f : A → B) → (df : RawChangeP f) →  IsDerivative (f raw⊕ df) (deriv-f⊕df f df)
  IsDerivative-deriv-f⊕df f df a da = update-diff (f (a ⊞ da) ⊞ df (a ⊞ da)) (f a ⊞ df a)

  FChange₀ : (A → B) → Set ℓ
  FChange₀ f₀ =
    Σ[ df ∈ RawChangeP f₀ ] (
      let f₁ = f₀ raw⊕ df
      in Σ[ f₁′ ∈ RawChange f₁ ] IsDerivative f₁ f₁′)

  FChange : FunBaseT → Set ℓ
  FChange (f₀ , f₀′ , IsDerivative-f₀-f₀′) = FChange₀ f₀

  _⊕_ : (f : FunBaseT) → FChange f → FunBaseT
  (f₀ , f₀′ , IsDerivative-f₀-f₀′) ⊕ (df , f₁′ , IsDerivative-f₁-f₁′) =
    let f₁ = f₀ raw⊕ df
    in (f₁ , f₁′ , IsDerivative-f₁-f₁′)

  -- Lemmas to transport across the f₁ ≅ f₀ equality.
  transport-base-f₀ : ∀ {f₀ f₁ : A → B} (eq : f₁ ≅ f₀) (f₀′ : RawChange f₀) (IsDerivative-f₀-f₀′ : IsDerivative f₀ f₀′) →
    Σ[ f₁′ ∈ RawChange f₁ ] (IsDerivative f₁ f₁′)
  transport-base-f₀ refl f₀′ IsDerivative-f₀-f₀′ = f₀′ , IsDerivative-f₀-f₀′

  transport-base-f : ∀ {f₀ g₀ : A → B} df →
    let g₁ = f₀ raw⊕ df
    in (eq : g₁ ≅ g₀) (g₀′ : RawChange g₀) (IsDerivative-g₀-g₀′ : IsDerivative g₀ g₀′) → FChange₀ f₀
  transport-base-f df eq g₀′ IsDerivative-g₀-g₀′ = df , transport-base-f₀ eq g₀′ IsDerivative-g₀-g₀′

  transport-base-f-eq : ∀ {f₀ f₁ : A → B}
    (eq : f₁ ≅ f₀) (f₀′ : RawChange f₀) (IsDerivative-f₀-f₀′ : IsDerivative f₀ f₀′) →
    (f₁ , transport-base-f₀ eq f₀′ IsDerivative-f₀-f₀′) P.≡ (f₀ , f₀′ , IsDerivative-f₀-f₀′)
  transport-base-f-eq refl f₀′ IsDerivative-f₀-f₀′ = P.refl

  f-nil : (f : FunBaseT) → FChange f
  f-nil (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    transport-base-f (rawnil f₀) (raw-update-nil f₀) f₀′ IsDerivative-f₀-f₀′

  f-update-nil : ∀ fstr → (fstr ⊕ f-nil fstr) P.≡ fstr
  f-update-nil (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    transport-base-f-eq (raw-update-nil f₀) f₀′ IsDerivative-f₀-f₀′

  _⊝_ : (g f : FunBaseT) → FChange f
  _⊝_ (g₀ , g₀′ , IsDerivative-g₀-g₀′) (f₀ , f₀′ , IsDerivative-f₀-f₀′) = transport-base-f (g₀ raw⊝ f₀) (raw-update-diff f₀ g₀) g₀′ IsDerivative-g₀-g₀′

  f-update-diff : ∀ gstr fstr → fstr ⊕ (gstr ⊝ fstr) P.≡ gstr
  f-update-diff (g₀ , g₀′ , IsDerivative-g₀-g₀′) (f₀ , f₀′ , IsDerivative-f₀-f₀′) = transport-base-f-eq (raw-update-diff f₀ g₀) g₀′ IsDerivative-g₀-g₀′

  changeAlgebra : ChangeAlgebra ℓ FunBaseT
  changeAlgebra = record
                    { Change = FChange
                    ; update = _⊕_
                    ; diff = _⊝_
                    ; nil = f-nil
                    ; isChangeAlgebra = record { update-diff = f-update-diff ; update-nil = f-update-nil }
                    }
