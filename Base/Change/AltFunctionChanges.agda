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

  FChange : FunBaseT → Set ℓ
  FChange (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    Σ[ df ∈ RawChangeP f₀ ] (
      let f₁ = f₀ raw⊕ df
      in Σ[ f₁′ ∈ RawChange f₁ ] IsDerivative f₁ f₁′)

  _⊕_ : (f : FunBaseT) → FChange f → FunBaseT
  (f₀ , f₀′ , IsDerivative-f₀-f₀′) ⊕ (df , f₁′ , IsDerivative-f₁-f₁′) =
    let f₁ = f₀ raw⊕ df
    in (f₁ , f₁′ , IsDerivative-f₁-f₁′)

  f-nil-eq : ∀ (f₀ : A → B) (f₀′ : RawChange f₀) (IsDerivative-f₀-f₀′ : IsDerivative f₀ f₀′) →
      Σ[ nil-f₀ ∈ RawChangeP f₀ ] (
        let f₁ = f₀ raw⊕ nil-f₀
        in Σ[ f₁′ ∈ RawChange f₁ ] Σ[ IsDerivative-f₁-f₁′ ∈ IsDerivative f₁ f₁′ ] (f₁ ≅ f₀ × f₁′ ≅ f₀′ × IsDerivative-f₁-f₁′ ≅ IsDerivative-f₀-f₀′))

  f-nil-eq f₀ f₀′ IsDerivative-f₀-f₀′ = df , f₁′ , IsDerivative-f₁-f₁′ , f₁≅f₀ , f₁′≅f₀′ , IsDerivative-f₁-f₁′≅IsDerivative-f₀-f₀′
    where
      df = rawnil f₀
      f₁ = f₀ raw⊕ df
      f₁≅f₀ = raw-update-nil f₀
      f₀≅f₁ = sym f₁≅f₀

      f₁′ = subst RawChange f₀≅f₁ f₀′

      f₁′≅f₀′ = subst-removable RawChange f₀≅f₁ f₀′
      f₀′≅f₁′ = sym f₁′≅f₀′

      IsDerivative-f₁-f₁′ = hsubst₂ IsDerivative f₀≅f₁ f₀′≅f₁′ IsDerivative-f₀-f₀′
      IsDerivative-f₁-f₁′≅IsDerivative-f₀-f₀′ = hsubst₂-removable IsDerivative f₀≅f₁ f₀′≅f₁′ IsDerivative-f₀-f₀′

  f-nil : (f : FunBaseT) → FChange f
  f-nil (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    let (df , f₁′ , IsDerivative-f₁-f₁′ , _ ) = f-nil-eq f₀ f₀′ IsDerivative-f₀-f₀′
    in df , f₁′ , IsDerivative-f₁-f₁′

  f-update-nil : ∀ fstr → (fstr ⊕ f-nil fstr) P.≡ fstr
  f-update-nil (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    let (df , f₁′ , IsDerivative-f₁-f₁′ , f₁≅f₀ , f₁′≅f₀′ , IsDerivative-f₁-f₁′≅IsDerivative-f₀-f₀′ ) = f-nil-eq f₀ f₀′ IsDerivative-f₀-f₀′
    in ≅-to-≡ (cong₃ (λ x y z → as' FunBaseT (x , y , z)) f₁≅f₀ f₁′≅f₀′ IsDerivative-f₁-f₁′≅IsDerivative-f₀-f₀′)

  f-diff-eq :
    ∀ (f₀ : A → B) (f₀′ : RawChange f₀) (IsDerivative-f₀-f₀′ : IsDerivative f₀ f₀′) →
      (g₀ : A → B) (g₀′ : RawChange g₀) (IsDerivative-g₀-g₀′ : IsDerivative g₀ g₀′) →
      Σ[ df ∈ RawChangeP f₀ ] (
        let g₁ = f₀ raw⊕ (g₀ raw⊝ f₀)
        in Σ[ g₁′ ∈ RawChange g₁ ] Σ[ IsDerivative-g₁-g₁′ ∈ IsDerivative g₁ g₁′ ] (g₁ ≅ g₀ × g₁′ ≅ g₀′ × IsDerivative-g₁-g₁′ ≅ IsDerivative-g₀-g₀′))
  f-diff-eq f₀ f₀′ IsDerivative-f₀-f₀′ g₀ g₀′ IsDerivative-g₀-g₀′
    = df , g₁′ , IsDerivative-g₁-g₁′ , g₁≅g₀ , g₁′≅g₀′ , IsDerivative-g₁-g₁′≅IsDerivative-g₀-g₀′
    where
      df = g₀ raw⊝ f₀
      g₁ = f₀ raw⊕ (g₀ raw⊝ f₀)
      g₁≅g₀ = raw-update-diff f₀ g₀
      g₀≅g₁ = sym g₁≅g₀

      g₁′ = subst RawChange g₀≅g₁ g₀′
      g₁′≅g₀′ = subst-removable RawChange g₀≅g₁ g₀′
      g₀′≅g₁′ = sym g₁′≅g₀′
      IsDerivative-g₁-g₁′ = hsubst₂ IsDerivative g₀≅g₁ g₀′≅g₁′ IsDerivative-g₀-g₀′
      IsDerivative-g₁-g₁′≅IsDerivative-g₀-g₀′ = hsubst₂-removable IsDerivative g₀≅g₁ g₀′≅g₁′ IsDerivative-g₀-g₀′

  _⊝_ : (g f : FunBaseT) → FChange f
  _⊝_ (g₀ , g₀′ , IsDerivative-g₀-g₀′) (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    let (df , g₁′ , IsDerivative-g₁-g₁′ , _) = f-diff-eq f₀ f₀′ IsDerivative-f₀-f₀′ g₀ g₀′ IsDerivative-g₀-g₀′
    in df , g₁′ , IsDerivative-g₁-g₁′

  -- _⊝_ : (g f : FunBaseT) → FChange f
  -- _⊝_ (g , g′ , IsDerivative-g-g′) (f , f′ , IsDerivative-f-f′)
  --   = g⊝f
  --   , cast-g′
  --   , hsubst₂ (IsDerivative {{CA}} {{CB}}) g≅f-raw⊕-g⊝f g′≅cast-g′ IsDerivative-g-g′
  --   where
  --     g⊝f = g raw⊝ f
  --     g≅f-raw⊕-g⊝f : g ≅ f raw⊕ g⊝f
  --     g≅f-raw⊕-g⊝f = sym (raw-update-diff f g)

  --     cast-g′ = subst RawChange g≅f-raw⊕-g⊝f g′

  --     g′≅cast-g′ : g′ ≅ cast-g′
  --     g′≅cast-g′ = sym (subst-removable RawChange g≅f-raw⊕-g⊝f g′)

  f-update-diff : ∀ gstr fstr → fstr ⊕ (gstr ⊝ fstr) P.≡ gstr
  f-update-diff (g₀ , g₀′ , IsDerivative-g₀-g₀′) (f₀ , f₀′ , IsDerivative-f₀-f₀′) =
    let (df , g₁′ , IsDerivative-g₁-g₁′ , g₁≅g₀ , g₁′≅g₀′ , IsDerivative-g₁-g₁′≅IsDerivative-g₀-g₀′ ) = f-diff-eq f₀ f₀′ IsDerivative-f₀-f₀′ g₀ g₀′ IsDerivative-g₀-g₀′
    in ≅-to-≡ (cong₃ (λ x y z → as' FunBaseT (x , y , z)) g₁≅g₀ g₁′≅g₀′ IsDerivative-g₁-g₁′≅IsDerivative-g₀-g₀′)

  changeAlgebra : ChangeAlgebra ℓ FunBaseT
  changeAlgebra = record
                    { Change = FChange
                    ; update = _⊕_
                    ; diff = _⊝_
                    ; nil = f-nil
                    ; isChangeAlgebra = record { update-diff = f-update-diff ; update-nil = f-update-nil }
                    }
  -- f-diff : (g f : FunBaseT) → FChange f
  -- f-diff (g , g′ , IsDerivative-g-g′) (f , f′ , IsDerivative-f-f′) = λ a → g a ⊟ f a


--   FChange : FunBaseT → Set ℓ
--   FChange (f , f′ , IsDerivative-f-f′) = RawChangeP f

--   _⊕_ : (f : FunBaseT) → FChange f → FunBaseT
--   (f , f′ , IsDerivative-f-f′) ⊕ df =
--     ( f raw⊕ df
--     , ( deriv-f⊕df f df
--       , IsDerivative-deriv-f⊕df f df
--       )
--     )
--   f-nil : (f : FunBaseT) → FChange f
--   f-nil (f , f′ , IsDerivative-f-f′) a = nil (f a)

--   f-diff : (g f : FunBaseT) → FChange f
--   f-diff (g , g′ , IsDerivative-g-g′) (f , f′ , IsDerivative-f-f′) = λ a → g a ⊟ f a

--   -- f-update-nil fstr₀@(f₀ , f′₀ , IsDerivative-f-f′₀) with ext (λ a → sym (update-nil (f₀ a)))
--   -- f-update-nil fstr₀@(f₀ , f′₀ , IsDerivative-f-f′₀) | refl = {!!}
--   -- gives:
-- {-
-- With clause pattern fstr₀@(f₀ , f′₀ , IsDerivative-f-f′₀) is not an
-- instance of its parent pattern
-- (_,_ f₀ (_,_ f′₀ IsDerivative-f-f′₀))
-- -}

--   f-update-nil : ∀ fstr → (fstr ⊕ f-nil fstr) ≡ fstr
--   f-update-nil fstr₀@(f₀ , f′₀ , IsDerivative-f-f′₀) = {!!}
--     where

--       nil-fstr = f-nil fstr₀

--       fstr₁ : FunBaseT
--       fstr₁ = fstr₀ ⊕ f-nil fstr₀

--       f₁ : A → B
--       f′₁ : RawChange f₁
--       IsDerivative-f-f′₁ : IsDerivative f₁ f′₁

--       f₁ = proj₁ fstr₁
--       f′₁ = proj₁ (proj₂ fstr₁)
--       IsDerivative-f-f′₁ = proj₂ (proj₂ fstr₁)
--       --(f₁ , f′₁ , IsDerivative-f-f′₁) = fstr₀ ⊕ f-nil fstr₀

--       f≡f : f₁ ≡ f₀
--       f≡f = raw-update-nil f₀

--       -- f′₁′ : RawChange f₀
--       -- f′₁′ = subst RawChange (sym f≡f) f′₁

--       -- -- f′₁≡f′₁′ : ∀ a → f′₁ a ≡ f′₁′ a
--       -- -- f′₁≡f′₁′ a = ?

--       -- f′≡f′a : ∀ a →  f′₁′ a ≡ f′₀ a
--       -- f′≡f′a a = {!!}

--       -- f′≡f′ : f′₀ ≡ f′₁′
--       -- f′≡f′ = ext f′≡f′a

--       -- -- IsDer≡ : IsDerivative-f-f′₁ ≡ IsDerivative-f-f′₀
--       -- -- IsDer≡ = ?

--   f-update-diff : ∀ gstr fstr → fstr ⊕ (f-diff gstr fstr) ≡ gstr
--   f-update-diff (f , f′ , IsDerivative-f-f′) (g , g′ , IsDerivative-g-g′) = {!!}
--     where
--       fg : f raw⊕ (g raw⊝ f) ≡ g
--       fg = raw-update-diff f g

--   changeAlgebra : ChangeAlgebra ℓ FunBaseT
--   changeAlgebra = record
--                     { Change = FChange
--                     ; update = _⊕_
--                     ; diff = f-diff
--                     ; nil = f-nil
--                     ; isChangeAlgebra = record { update-diff = f-update-diff ; update-nil = f-update-nil }
--                     }
