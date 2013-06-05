module Data.NatBag.Properties where

import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality
open import Data.NatBag
open import Data.Integer
open import Data.Sum hiding (map)

-- This import is too slow.
-- It causes Agda 2.3.2 to use so much memory that cai's
-- computer with 4GB RAM begins to thresh.
--
-- open import Data.Integer.Properties using (n⊖n≡0)
n⊖n≡0 : ∀ n → n ⊖ n ≡ + 0
n⊖n≡0 ℕ.zero    = refl
n⊖n≡0 (ℕ.suc n) = n⊖n≡0 n


----------------
-- Statements --
----------------


b\\b=∅ : ∀ {b : Bag} → b \\ b ≡ empty

∅++b=b : ∀ {b : Bag} → empty ++ b ≡ b

b\\∅=b : ∀ {b : Bag} → b \\ empty ≡ b

++d=\\-d : ∀ {b d : Bag} → b ++ d ≡ b \\ map₂ -_ d

b++[d\\b]=d : ∀ {b d : Bag} → b ++ (d \\ b) ≡ d


------------
-- Proofs --
------------

i-i=0 : ∀ {i : ℤ} → (i - i) ≡ (+ 0)
i-i=0 {+ ℕ.zero} = refl
i-i=0 {+ ℕ.suc n} = n⊖n≡0 n
i-i=0 { -[1+ n ]} = n⊖n≡0 n

absurd : Nonzero (+ 0) → ∀ {A : Set} → A
absurd ()

-- Here to please the termination checker.
neb\\neb=∅ : ∀ {neb : NonemptyBag} → zipNonempty _-_ neb neb ≡ empty
neb\\neb=∅ {singleton i i≠0} with nonzero? (i - i)
... | inj₁ _ = refl
... | inj₂ 0≠0 rewrite i-i=0 {i} = absurd 0≠0
neb\\neb=∅ {i ∷ neb} with nonzero? (i - i)
... | inj₁ _ rewrite neb\\neb=∅ {neb} = refl
... | inj₂ 0≠0 rewrite neb\\neb=∅ {neb} | i-i=0 {i} = absurd 0≠0

++d=\\-d {inj₁ ∅} {inj₁ ∅} = refl
++d=\\-d {inj₁ ∅} {inj₂ (i ∷ y)} = {!!}
++d=\\-d {inj₂ y} {d} = {!!}
++d=\\-d {inj₁ ∅} {inj₂ (singleton i i≠0)}
  rewrite ∅++b=b {inj₂ (singleton i i≠0)}
  with nonzero? i | nonzero? (+ 0 - i)
... | inj₂ _ | inj₂ 0-i≠0 =
  begin
    {!!}
  ≡⟨ {!!} ⟩
    {!inj₂ (singleton (- i) ?)!}
  ∎ where open ≡-Reasoning
... | inj₁ i=0 | _ rewrite i=0 = absurd i≠0
++d=\\-d {inj₁ ∅} {inj₂ (singleton (+ 0) i≠0)} | _ | _ = absurd i≠0
++d=\\-d {inj₁ ∅} {inj₂ (singleton (+ (ℕ.suc n)) i≠0)}
  | inj₂ (positive .n) | inj₁ ()
++d=\\-d {inj₁ ∅} {inj₂ (singleton -[1+ n ] i≠0)}
  | inj₂ (negative .n) | inj₁ ()

b\\b=∅ {inj₁ ∅} = refl
b\\b=∅ {inj₂ neb} = neb\\neb=∅ {neb}

∅++b=b {b} = {!!}

b\\∅=b {b} = {!!}

negate : ∀ {i} → Nonzero i → Nonzero (- i)
negate (negative n) = positive n
negate (positive n) = negative n

negate′ : ∀ {i} → (i≠0 : Nonzero i) → Nonzero (+ 0 - i)
negate′ { -[1+ n ]} (negative .n) = positive n
negate′ {+ .(ℕ.suc n)} (positive n) = negative n

0-i=-i : ∀ {i} → + 0 - i ≡ - i
0-i=-i { -[1+ n ]} = refl -- cases are split, for arguments to
0-i=-i {+ ℕ.zero}  = refl -- refl are different.
0-i=-i {+ ℕ.suc n} = refl

rewrite-singleton :
  ∀ (i : ℤ) (0-i≠0 : Nonzero (+ 0 - i)) ( -i≠0 : Nonzero (- i)) →
    singleton (+ 0 - i) 0-i≠0 ≡ singleton (- i) -i≠0
rewrite-singleton (+ ℕ.zero) () ()
rewrite-singleton (+ ℕ.suc n) (negative .n) (negative .n) = refl
rewrite-singleton ( -[1+ n ]) (positive .n) (positive .n) = refl

negateSingleton : ∀ {i i≠0} →
  mapNonempty₂ (λ j → + 0 - j) (singleton i i≠0)
  ≡
  inj₂ (singleton (- i) (negate i≠0))

-- Fun fact:
-- Pattern-match on implicit parameters in the first two
-- cases results in rejection by Agda.
negateSingleton {i} {i≠0} with nonzero? i | nonzero? (+ 0 - i)
negateSingleton | inj₂ (negative n) | inj₁ ()
negateSingleton | inj₂ (positive n) | inj₁ ()
negateSingleton {_} {i≠0} | inj₁ i=0 | _ rewrite i=0 = absurd i≠0
negateSingleton {i} {i≠0} | inj₂ _ | inj₂ 0-i≠0 =
  begin -- Reasoning done in 1 step. Included for clarity only.
    inj₂ (singleton (+ 0 + - i) 0-i≠0)
  ≡⟨ cong inj₂ (rewrite-singleton i 0-i≠0 (negate i≠0)) ⟩
    inj₂ (singleton (- i) (negate i≠0))
  ∎  where open ≡-Reasoning

b++[∅\\b]=∅ : ∀ {b} → b ++ (empty \\ b) ≡ empty
b++[∅\\b]=∅ {inj₁ ∅} = refl
b++[∅\\b]=∅ {inj₂ (singleton i i≠0)} =
  begin
    inj₂ (singleton i i≠0) ++
      mapNonempty₂ (λ j → + 0 - j) (singleton i i≠0)
{-
  ≡⟨ cong₂ _++_ {x = inj₂ (singleton i i≠0)} refl
                (negateSingleton {i} {i≠0}) ⟩
    inj₂ (singleton i i≠0) ++ inj₂ (singleton (- i) (negate i≠0))
-}
  ≡⟨ {!!} ⟩
    inj₁ ∅
  ∎ where open ≡-Reasoning
b++[∅\\b]=∅ {inj₂ (i ∷ y)} = {!!}

b++[d\\b]=d {inj₁ ∅} {d} rewrite b\\∅=b {d} | ∅++b=b {d} = refl
b++[d\\b]=d {b} {inj₁ ∅} = b++[∅\\b]=∅ {b}
b++[d\\b]=d {inj₂ neb} {inj₂ y} = {!!}

