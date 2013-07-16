module Theorem.GroupsPopl14 where

-- Theorems regarding the group structure of integers and bags
-- as needed by Calculus Popl14

open import Relation.Binary.PropositionalEquality
open import Structure.Bag.Popl14
open import Data.Integer

n+[m-n]=m : ∀ {n m} → n + (m - n) ≡ m
n+[m-n]=m {n} {m} =
  begin
    n + (m - n)
  ≡⟨ cong (λ hole → n + hole) (commutative-int m (- n)) ⟩
    n + (- n + m)
  ≡⟨ sym (associative-int n (- n) m) ⟩
    (n - n) + m
  ≡⟨ cong (λ hole → hole + m) (right-inv-int n) ⟩
    (+ 0) + m
  ≡⟨ left-id-int m ⟩
    m
  ∎ where open ≡-Reasoning

a++[b\\a]=b : ∀ {a b} → a ++ (b \\ a) ≡ b
a++[b\\a]=b {b} {d} = trans
  (cong (λ hole → b ++ hole) (commutative-bag d (negateBag b))) (trans
  (sym (associative-bag b (negateBag b) d)) (trans
  (cong (λ hole → hole ++ d) (right-inv-bag b))
  (left-id-bag d)))
