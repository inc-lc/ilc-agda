module Thesis.SIRelBigStep.ArithExtra where

open import Relation.Binary.PropositionalEquality
open import Data.Nat public
open import Data.Nat.Properties public
open import Relation.Binary hiding (_⇒_)

lt1 : ∀ {k n} → k < n → k ≤ n
lt1 (s≤s p) = ≤-step p

m∸n≤m : ∀ m n → m ∸ n ≤ m
m∸n≤m m zero = ≤-refl
m∸n≤m zero (suc n) = z≤n
m∸n≤m (suc m) (suc n) = ≤-step (m∸n≤m m n)

suc∸ : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
suc∸ m zero z≤n = refl
suc∸ (suc m) (suc n) (s≤s n≤m) = suc∸ m n n≤m

sub∸ : ∀ m n o → m + n ≤ o → n ≤ o ∸ m
sub∸ m n o n+m≤o rewrite +-comm m n | cong (_≤ o ∸ m) (sym (m+n∸n≡m n m)) = ∸-mono n+m≤o (≤-refl {m})
