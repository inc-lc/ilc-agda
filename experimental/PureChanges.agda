module experimental.PureChanges where

open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Bool hiding (_≟_)
open import Data.List
open import Algebra

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; module ≡-Reasoning)
open import Relation.Nullary
open import Relation.Nullary.Decidable
--import Relation.Binary.HeterogeneousEquality as H

open import DecidableEq ℕ _≟_

Base : Set
Base = ℕ

Change₁ : Set
Change₁ = ℕ × ℕ

Change : Set
Change = List Change₁

apply₁ : Change₁ → Base → Base
apply₁ (proj₁ , proj₂) v = if ⌊ proj₁ ≟ v ⌋ then proj₂ else v

apply : Change → Base → Base
apply = flip (foldr apply₁)

diff : Base → Base → Change
diff new old = [ old , new ]

compose : Change → Change → Change
compose = _++_

open import Data.List.Properties
compose-IsFold : ∀ {xs ys} → compose xs ys ≡ foldr _∷_ ys xs
compose-IsFold {xs} {ys} = ++IsFold xs ys

_⊕_ = apply
_⊝_ = diff
_⊚_ = compose

infixl 6 _⊕_ _⊝_ _⊚_ -- as with + - in GHC.Num


≡-cong₂ = cong₂

≡-diff : ∀ {v₁ v₂ v₃ v₄} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → diff v₁ v₃ ≡ diff v₂ v₄
≡-diff = ≡-cong₂ diff

≡-apply : ∀ {dv₁ dv₂} {v₁ v₂} →
  dv₁ ≡ dv₂ → v₁ ≡ v₂ → apply dv₁ v₁ ≡ apply dv₂ v₂
≡-apply = ≡-cong₂ apply

apply-diff : ∀ {v₁ v₂} → apply (diff v₂ v₁) v₁ ≡ v₂
apply-diff {v₁} {v₂} = 
  begin
    apply (diff v₂ v₁) v₁
  ≡⟨⟩
    (if ⌊ v₁ ≟ v₁ ⌋ then v₂ else v₁)
  ≡⟨ cong (λ x → if x then v₂ else v₁) (v≟v-true v₁) ⟩ 
    (if true then v₂ else v₁)
  ≡⟨⟩
    v₂
  ∎
  where
    open ≡-Reasoning

diff-apply : ∀ ds s → ds ⊕ s ⊝ s ≡ ds
diff-apply [] s = {!!}
diff-apply ((proj₁ , proj₂) ∷ ds) s rewrite diff-apply ds s = {!refl!}

apply-compose : ∀ v dv₁ dv₂ →
  (dv₁ ⊚ dv₂) ⊕ v ≡ dv₁ ⊕ (dv₂ ⊕ v)
apply-compose v [] dv₂ = refl
apply-compose v (x ∷ dv₁) dv₂ rewrite apply-compose v dv₁ dv₂ = refl

compose-assoc : ∀ dv₁ dv₂ dv₃ → (dv₁ ⊚ dv₂) ⊚ dv₃ ≡ dv₁ ⊚ (dv₂ ⊚ dv₃)
compose-assoc = let open Monoid (monoid Change₁) in assoc

-- compose-assoc (old₁ , new₁) (old₂ , new₂) (old₃ , new₃) with new₁ ≟ old₂ | new₂ ≟ old₃
-- compose-assoc (old₁ , new₁) (.new₁ , new₂) (.new₂ , new₃) | yes refl | yes refl = let
--     open ≡-Reasoning in
--   begin
--     (if ⌊ new₂ ≟ new₂ ⌋ then old₁ , new₃ else old₁ , new₂)
--   ≡⟨ cong (λ b → if b then old₁ , new₃ else old₁ , new₂) (v≟v-true new₂) ⟩
--     old₁ , new₃
--   ≡⟨ sym (cong (λ b → if b then old₁ , new₃ else old₁ , new₁) (v≟v-true new₁)) ⟩
--     (if ⌊ new₁ ≟ new₁ ⌋ then old₁ , new₃ else old₁ , new₁)
--   ∎
-- compose-assoc (old₁ , new₁) (.new₁ , new₂) (old₃ , new₃) | yes refl | no ¬p = {!!}
-- compose-assoc (old₁ , new₁) (old₂ , new₂) (old₃ , new₃) | no ¬p | yes p = {!!}
-- compose-assoc (old₁ , new₁) (old₂ , new₂) (old₃ , new₃) | no ¬p | no ¬p₁ = let
--     open ≡-Reasoning in
--   begin
--     (if ⌊ new₁ ≟ old₃ ⌋ then old₁ , new₃ else old₁ , new₁)
--   ≡⟨ cong (λ b → if b then old₁ , new₃ else old₁ , new₁) (≢→≟false {new₁} {old₃} {!
--   {- This hole cannot be filled - one can easily construct a counterexample. -}
-- !}) ⟩
--     old₁ , new₁
--   ≡⟨ sym (cong (λ b → if b then old₁ , new₂ else old₁ , new₁) (≢→≟false ¬p)) ⟩
--     (if ⌊ new₁ ≟ old₂ ⌋ then old₁ , new₂ else old₁ , new₁)
--   ∎
