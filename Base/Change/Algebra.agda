module Base.Change.Algebra where

open import Relation.Binary.PropositionalEquality
open import Level

-- Change Algebras

record IsChangeAlgebra
    {c} {d}
    {Carrier : Set c}
    (Change : Carrier → Set d)
    (update : (v : Carrier) (dv : Change v) → Carrier)
    (diff : (u v : Carrier) → Change v) : Set (c ⊔ d) where
  field
    update-diff : ∀ u v → update v (diff u v) ≡ u

  nil : ∀ v → Change v
  nil v = diff v v

  update-nil : ∀ v → update v (nil v) ≡ v
  update-nil v = update-diff v v

record ChangeAlgebra {c} ℓ
    (Carrier : Set c) : Set (c ⊔ suc ℓ) where
  field
    Change : Carrier → Set ℓ
    update : (v : Carrier) (dv : Change v) → Carrier
    diff : (u v : Carrier) → Change v

    isChangeAlgebra : IsChangeAlgebra Change update diff


  infixl 6 update diff

  open IsChangeAlgebra isChangeAlgebra public

open ChangeAlgebra {{...}} public
  using
    ( update-diff
    ; update-nil
    ; nil
    )
  renaming
    ( Change to Δ
    ; update to _⊞_
    ; diff to _⊟_
    )
