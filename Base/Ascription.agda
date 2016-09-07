module Base.Ascription where

-- Encode infix ascription.
as' : ∀ {ℓ} (A : Set ℓ) (a : A) → A
as' _ a = a
syntax as' A a = a as A
