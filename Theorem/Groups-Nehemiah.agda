------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- About the group structure of integers and bags for Nehemiah plugin.
------------------------------------------------------------------------

module Theorem.Groups-Nehemiah where

open import Structure.Bag.Nehemiah public

open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Algebra.Structures

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

4-way-shuffle : ∀ {A : Set} {f neg} {z a b c d : A}
  {{abelian : IsAbelianGroup _≡_ f z neg}} →
  f (f a b) (f c d) ≡ f (f a c) (f b d)
4-way-shuffle {f = f} {z = z} {a} {b} {c} {d} {{abelian}} =
  let
    assoc = associative abelian
    cmute = commutative abelian
  in
    begin
      f (f a b) (f c d)
    ≡⟨ assoc a b (f c d) ⟩
      f a (f b (f c d))
    ≡⟨ cong (f a) (sym (assoc b c d)) ⟩
      f a (f (f b c) d)
    ≡⟨ cong (λ hole → f a (f hole d)) (cmute b c) ⟩
      f a (f (f c b) d)
    ≡⟨ cong (f a) (assoc c b d) ⟩
      f a (f c (f b d))
    ≡⟨ sym (assoc a c (f b d)) ⟩
      f (f a c) (f b d)
    ∎ where open ≡-Reasoning

ab·cd=ac·bd : ∀ {a b c d : Bag} →
  (a ++ b) ++ (c ++ d) ≡ (a ++ c) ++ (b ++ d)
ab·cd=ac·bd {a} {b} {c} {d} =
  4-way-shuffle {a = a} {b} {c} {d} {{abelian-bag}}

mn·pq=mp·nq : ∀ {m n p q : ℤ} →
  (m + n) + (p + q) ≡ (m + p) + (n + q)
mn·pq=mp·nq {m} {n} {p} {q} =
  4-way-shuffle {a = m} {n} {p} {q} {{abelian-int}}

inverse-unique : ∀ {A : Set} {f neg} {z a b : A}
  {{abelian : IsAbelianGroup _≡_ f z neg}} →
  f a b ≡ z → b ≡ neg a

inverse-unique {f = f} {neg} {z} {a} {b} {{abelian}} ab=z =
  let
    assoc = associative abelian
    cmute = commutative abelian
  in
    begin
      b
    ≡⟨ sym (left-identity abelian b) ⟩
      f z b
    ≡⟨ cong (λ hole → f hole b) (sym (left-inverse abelian a)) ⟩
      f (f (neg a) a) b
    ≡⟨ assoc (neg a) a b ⟩
      f (neg a) (f a b)
    ≡⟨ cong (f (neg a)) ab=z ⟩
      f (neg a) z
    ≡⟨ right-identity abelian (neg a) ⟩
      neg a
    ∎ where
      open ≡-Reasoning
      eq1 : f (neg a) (f a b) ≡ f (neg a) z
      eq1 rewrite ab=z = cong (f (neg a)) refl

distribute-neg : ∀ {A : Set} {f neg} {z a b : A}
  {{abelian : IsAbelianGroup _≡_ f z neg}} →
  f (neg a) (neg b) ≡ neg (f a b)
distribute-neg {f = f} {neg} {z} {a} {b} {{abelian}} = inverse-unique
  {{abelian}}
  (begin
    f (f a b) (f (neg a) (neg b))
  ≡⟨ 4-way-shuffle {{abelian}} ⟩
    f (f a (neg a)) (f b (neg b))
  ≡⟨ cong₂ f (inverse a) (inverse b) ⟩
    f z z
  ≡⟨ left-identity abelian z ⟩
    z
  ∎) where
     open ≡-Reasoning
     inverse = right-inverse abelian

-a·-b=-ab : ∀ {a b : Bag} →
  negateBag a ++ negateBag b ≡ negateBag (a ++ b)
-a·-b=-ab {a} {b} = distribute-neg {a = a} {b} {{abelian-bag}}

-m·-n=-mn : ∀ {m n : ℤ} →
  (- m) + (- n) ≡ - (m + n)
-m·-n=-mn {m} {n} = distribute-neg {a = m} {n} {{abelian-int}}

[a++b]\\a=b : ∀ {a b} → (a ++ b) \\ a ≡ b
[a++b]\\a=b {b} {d} =
  begin
    (b ++ d) \\ b
  ≡⟨ cong (λ hole → hole \\ b) (commutative-bag b d) ⟩
    (d ++ b) \\ b
  ≡⟨ associative-bag d b (negateBag b) ⟩
    d ++ (b \\ b)
  ≡⟨ cong (_++_ d) (right-inv-bag b) ⟩
    d ++ emptyBag
  ≡⟨ right-id-bag d ⟩
    d
  ∎ where open ≡-Reasoning

open import Algebra.Properties.AbelianGroup (record
                                               { Carrier = Bag
                                               ; _≈_ = _≡_
                                               ; _∙_ = _++_
                                               ; ε = emptyBag
                                               ; _⁻¹ = negateBag
                                               ; isAbelianGroup = abelian-bag
                                               })

negateEmptyBag-emptyBag : negateBag emptyBag ≡ emptyBag
negateEmptyBag-emptyBag = right-identity-unique emptyBag (negateBag emptyBag) (right-inverse abelian-bag emptyBag)

a++negateBagEmptyBag≡a : ∀ a → a ++ negateBag emptyBag ≡ a
a++negateBagEmptyBag≡a a rewrite negateEmptyBag-emptyBag = right-id-bag a
