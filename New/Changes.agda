module New.Changes where

open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Unit
open import Data.Product

record IsChAlg {ℓ : Level} (A : Set ℓ) (Ch : Set ℓ) : Set (suc ℓ) where
  field
    _⊕_ : A → Ch → A
    _⊝_ : A → A → Ch
    valid : A → Ch → Set ℓ
    ⊝-valid : ∀ (a b : A) → valid a (b ⊝ a)
    ⊕-⊝ : (b a : A) → a ⊕ (b ⊝ a) ≡ b
  infixl 6 _⊕_ _⊝_

  nil : A → Ch
  nil a = a ⊝ a
  nil-valid : (a : A) → valid a (nil a)
  nil-valid a = ⊝-valid a a

  Δ : A → Set ℓ
  Δ a = Σ[ da ∈ Ch ] (valid a da)

  update-diff = ⊕-⊝
  update-nil : (a : A) → a ⊕ nil a ≡ a
  update-nil a = update-diff a a

record ChAlg {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
  field
    Ch : Set ℓ
    isChAlg : IsChAlg A Ch
  open IsChAlg isChAlg public

open ChAlg {{...}} public hiding (Ch)
Ch : ∀ {ℓ} (A : Set ℓ) → {{CA : ChAlg A}} → Set ℓ
Ch A {{CA}} = ChAlg.Ch CA

-- Huge hack, but it does gives the output you want to see in all cases I've seen.

{-# DISPLAY IsChAlg.valid x = valid #-}
{-# DISPLAY ChAlg.valid x = valid #-}
{-# DISPLAY IsChAlg._⊕_ x = _⊕_ #-}
{-# DISPLAY ChAlg._⊕_ x = _⊕_ #-}
{-# DISPLAY IsChAlg.nil x = nil #-}
{-# DISPLAY ChAlg.nil x = nil #-}
{-# DISPLAY IsChAlg._⊝_ x = _⊝_ #-}
{-# DISPLAY ChAlg._⊝_ x = _⊝_ #-}

module _ {ℓ₁} {ℓ₂}
  {A : Set ℓ₁} {B : Set ℓ₂} {{CA : ChAlg A}} {{CB : ChAlg B}} where
  private
    fCh = A → Ch A → Ch B
    _f⊕_ : (A → B) → fCh → A → B
    _f⊕_ = λ f df a → f a ⊕ df a (nil a)
    _f⊝_ : (g f : A → B) → fCh
    _f⊝_ = λ g f a da → g (a ⊕ da) ⊝ f a
  open ≡-Reasoning
  open import Postulate.Extensionality

  IsDerivative : ∀ (f : A → B) → (df : fCh) → Set (ℓ₁ ⊔ ℓ₂)
  IsDerivative f df = ∀ a da (v : valid a da) → f (a ⊕ da) ≡ f a ⊕ df a da

  instance
    funCA : ChAlg (A → B)
  private
    funUpdateDiff : ∀ g f a → (f f⊕ (g f⊝ f)) a ≡ g a
  funUpdateDiff g f a rewrite update-nil a = update-diff (g a) (f a)
  funCA = record
    { Ch = A → Ch A → Ch B
    ; isChAlg = record
      { _⊕_ = _f⊕_
      ; _⊝_ = _f⊝_
      ; valid = λ f df → ∀ a da (v : valid a da) →
        valid (f a) (df a da) ×
        (f f⊕ df) (a ⊕ da) ≡ f a ⊕ df a da
      ; ⊝-valid = λ f g a da (v : valid a da) →
         ⊝-valid (f a) (g (a ⊕ da))
        , ( begin
          f (a ⊕ da) ⊕ (g (a ⊕ da ⊕ nil (a ⊕ da)) ⊝ f (a ⊕ da))
        ≡⟨ cong (λ □ → f (a ⊕ da) ⊕ (g □ ⊝ f (a ⊕ da)))
             (update-nil (a ⊕ da)) ⟩
          f (a ⊕ da) ⊕ (g (a ⊕ da) ⊝ f (a ⊕ da))
        ≡⟨ update-diff (g (a ⊕ da)) (f (a ⊕ da)) ⟩
          g (a ⊕ da)
        ≡⟨ sym (update-diff (g (a ⊕ da)) (f a)) ⟩
          f a ⊕ (g (a ⊕ da) ⊝ f a)
        ∎)
      ; ⊕-⊝ = λ g f → ext (funUpdateDiff g f)
      } }

  nil-is-derivative : ∀ (f : A → B) → IsDerivative f (nil f)
  nil-is-derivative f a da v =
    begin
      f (a ⊕ da)
    ≡⟨ sym (cong (λ □ → □ (_⊕_ a da)) (update-nil f)) ⟩
      (f ⊕ nil f) (a ⊕ da)
    ≡⟨ proj₂ (nil-valid f a da v) ⟩
      f a ⊕ (nil f a da)
    ∎

  private
    _p⊕_ : A × B → Ch A × Ch B → A × B
    _p⊕_ (a , b) (da , db) = a ⊕ da , b ⊕ db
    _p⊝_ : A × B → A × B → Ch A × Ch B
    _p⊝_ (a2 , b2) (a1 , b1) = a2 ⊝ a1 , b2 ⊝ b1
    pvalid : A × B → Ch A × Ch B → Set (ℓ₂ ⊔ ℓ₁)
    pvalid (a , b) (da , db) = valid a da × valid b db
    p⊝-valid : (p1 p2 : A × B) → pvalid p1 (p2 p⊝ p1)
    p⊝-valid (a1 , b1) (a2 , b2) = ⊝-valid a1 a2 , ⊝-valid b1 b2
    p⊕-⊝ : (p2 p1 : A × B) → p1 p⊕ (p2 p⊝ p1) ≡ p2
    p⊕-⊝ (a2 , b2) (a1 , b1) = cong₂ _,_ (⊕-⊝ a2 a1) (⊕-⊝ b2 b1)
  instance
    pairCA : ChAlg (A × B)
  pairCA = record
    { Ch = Ch A × Ch B
    ; isChAlg = record
    { _⊕_ = _p⊕_
    ; _⊝_ = _p⊝_
    ; valid = pvalid
    ; ⊝-valid = p⊝-valid
    ; ⊕-⊝ = p⊕-⊝
    } }

open import Data.Integer
open import Theorem.Groups-Nehemiah

instance
  intCA : ChAlg ℤ
intCA = record
  { Ch = ℤ
  ; isChAlg = record
  { _⊕_ = _+_
  ; _⊝_ = _-_
  ; valid = λ a b → ⊤
  ; ⊝-valid = λ a b → tt
  ; ⊕-⊝ = λ b a → n+[m-n]=m {a} {b} } }
