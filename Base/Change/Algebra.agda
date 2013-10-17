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

-- Families of change algebras

record ChangeAlgebraFamily {a p} ℓ {A : Set a} (P : A → Set p): Set (suc ℓ ⊔ p ⊔ a) where
  constructor
    family
  field
    change-algebra : ∀ x → ChangeAlgebra ℓ (P x)

  module _ x where
    open ChangeAlgebra (change-algebra x) public

module Family = ChangeAlgebraFamily {{...}}

open Family public
  using
    (
    )
  renaming
    ( Change to Δ₍_₎
    ; nil to nil₍_₎
    ; update-diff to update-diff₍_₎
    ; update-nil to update-nil₍_₎
    ; change-algebra to change-algebra₍_₎
    )

infixl 6 update′ diff′

update′ = Family.update
syntax update′ x v dv = v ⊞₍ x ₎ dv

diff′ = Family.diff
syntax diff′ x u v = u ⊟₍ x ₎ v

-- Abelian groups induce change algebras

open import Algebra.Structures
open import Data.Product
open import Function

module GroupChanges
    {a} (A : Set a) {_⊕_} {ε} {_⁻¹}
    {{isAbelianGroup : IsAbelianGroup {A = A} _≡_ _⊕_ ε _⁻¹}}
  where
    open IsAbelianGroup isAbelianGroup
      hiding
        ( refl
        )
      renaming
        ( _-_ to _⊝_
        ; ∙-cong to _⟨⊕⟩_
        )

    open ≡-Reasoning

    changeAlgebra : ChangeAlgebra a A
    changeAlgebra = record
      { Change = const A
      ; update = _⊕_
      ; diff = _⊝_
      ; isChangeAlgebra = record
        { update-diff = λ u v →
            begin
              v ⊕ (u ⊝ v)
            ≡⟨ comm _ _ ⟩
              (u ⊝ v ) ⊕ v
            ≡⟨⟩
              (u ⊕ (v ⁻¹)) ⊕ v
            ≡⟨ assoc _ _ _ ⟩
              u ⊕ ((v ⁻¹) ⊕ v)
            ≡⟨  refl ⟨⊕⟩ proj₁ inverse v  ⟩
              u ⊕ ε
            ≡⟨  proj₂ identity u ⟩
              u
            ∎
        }
      }

-- Function changes

module FunctionChanges
    {a} {b} {c} {d} (A : Set a) (B : Set b) {{CA : ChangeAlgebra c A}} {{CB : ChangeAlgebra d B}}
  where
    record FunctionChange (f : A → B) : Set (a ⊔ b ⊔ c ⊔ d) where
      constructor
        cons
      field
        apply : (a : A) (da : Δ a) →
          Δ (f a)
        correct : (a : A) (da : Δ a) →
          f (a ⊞ da) ⊞ apply (a ⊞ da) (nil (a ⊞ da)) ≡ f a ⊞ apply a da

    open FunctionChange
    open ≡-Reasoning
    open import Postulate.Extensionality

    changeAlgebra : ChangeAlgebra (a ⊔ b ⊔ c ⊔ d) (A → B)
    changeAlgebra = record
      { Change = FunctionChange
      ; update = λ f df a → f a ⊞ apply df a (nil a)
      ; diff = λ g f → record
        { apply = λ a da → g (a ⊞ da) ⊟ f a
        ; correct = λ a da →
          begin
            f (a ⊞ da) ⊞ (g ((a ⊞ da) ⊞ nil (a ⊞ da)) ⊟ f (a ⊞ da))
          ≡⟨ cong (λ □ → f (a ⊞ da) ⊞ (g □ ⊟ f (a ⊞ da)))
               (update-nil (a ⊞ da)) ⟩
            f (a ⊞ da) ⊞ (g (a ⊞ da) ⊟ f (a ⊞ da))
          ≡⟨ update-diff (g (a ⊞ da)) (f (a ⊞ da)) ⟩
            g (a ⊞ da)
          ≡⟨ sym (update-diff (g (a ⊞ da)) (f a)) ⟩
            f a ⊞ (g (a ⊞ da) ⊟ f a)
          ∎
        }
      ; isChangeAlgebra = record
        { update-diff = λ g f → ext (λ a →
          begin
            f a ⊞ (g (a ⊞ nil a) ⊟ f a)
          ≡⟨ cong (λ □ → f a ⊞ (g □ ⊟ f a)) (update-nil a) ⟩
            f a ⊞ (g a ⊟ f a)
          ≡⟨ update-diff (g a) (f a) ⟩
            g a
          ∎)
        }
      }
