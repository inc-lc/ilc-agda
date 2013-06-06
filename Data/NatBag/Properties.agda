module Data.NatBag.Properties where

import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality
open import Data.NatBag
open import Data.Integer
open import Data.Sum hiding (map)
open import Data.Product hiding (map)

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

-- Caution: Please convert all implicit bag argument to
-- instance bag argument in the next iteration so that
-- using the lemmas here incurs less typing overhead.
-- Leave the implicit arguments on multivariate lemmas,
-- though.
--
-- TODO: Convert bags from a sum to an ADT so that
-- constructor names give hints to the bag type,
-- and a set-theoretic development can write things
-- like ∀ {b} → ∅ ⊆ b.


b\\b=∅ : ∀ {b} → b \\ b ≡ empty

∅++b=b : ∀ {b} → empty ++ b ≡ b

b\\∅=b : ∀ {b} → b \\ empty ≡ b

b++∅=b : ∀ {{b}} → b ++ empty ≡ b

b++[d\\b]=d : ∀ {b d} → b ++ (d \\ b) ≡ d

[b++d]\\b=d : ∀ {b d} → (b ++ d) \\ b ≡ d

------------
-- Proofs --
------------

b++∅=b = {!!}

i-i=0 : ∀ {i : ℤ} → (i - i) ≡ (+ 0)
i-i=0 {+ ℕ.zero} = refl
i-i=0 {+ ℕ.suc n} = n⊖n≡0 n
i-i=0 { -[1+ n ]} = n⊖n≡0 n

-- Debug tool
-- Lets you try out inhabitance of any type anywhere
absurd! : ∀ {B C : Set} → 0 ≡ 1 → B → {x : B} → C
absurd! ()

-- Specialized absurdity needed to type check.
-- λ () hasn't enough information sometimes.
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

absurd[i-i≠0] : ∀ {i} → Nonzero (i - i) → ∀ {A : Set} → A
absurd[i-i≠0] {+ ℕ.zero} = absurd
absurd[i-i≠0] {+ ℕ.suc n} = absurd[i-i≠0] { -[1+ n ]}
absurd[i-i≠0] { -[1+ ℕ.zero ]} = absurd
absurd[i-i≠0] { -[1+ ℕ.suc n ]} = absurd[i-i≠0] { -[1+ n ]}

annihilate : ∀ {i i≠0} →
  inj₂ (singleton i i≠0) ++ inj₂ (singleton (- i) (negate i≠0)) ≡ inj₁ ∅

annihilate {i} with nonzero? (i - i)
... | inj₁ i-i=0 = λ {i≠0} → refl
... | inj₂ i-i≠0 = absurd[i-i≠0] {i} i-i≠0
{-
Follow-up question to
https://github.com/ps-mr/ilc/commit/978e3f94e70762904e077bb4d51d6b7b17695103#commitcomment-3367105

Mysterious error message when the case above is replaced by the one
below.

annihilate {i} with i - i
... | w = ?
-}

b++[∅\\b]=∅ : ∀ {b} → b ++ (empty \\ b) ≡ empty
b++[∅\\b]=∅ {inj₁ ∅} = refl
b++[∅\\b]=∅ {inj₂ (singleton i i≠0)} =
  begin
    inj₂ (singleton i i≠0) ++
      mapNonempty₂ (λ j → + 0 - j) (singleton i i≠0)
  ≡⟨ cong₂ _++_ {x = inj₂ (singleton i i≠0)} refl
                (negateSingleton {i} {i≠0}) ⟩
    inj₂ (singleton i i≠0) ++ inj₂ (singleton (- i) (negate i≠0))
  ≡⟨ annihilate {i} {i≠0} ⟩
    inj₁ ∅
  ∎ where open ≡-Reasoning

b++[∅\\b]=∅ {inj₂ (i ∷ y)} = ?

b++[d\\b]=d {inj₁ ∅} {d} rewrite b\\∅=b {d} | ∅++b=b {d} = refl
b++[d\\b]=d {b} {inj₁ ∅} = b++[∅\\b]=∅ {b}
b++[d\\b]=d {inj₂ b} {inj₂ d} = {!!}

[b++d]\\b=d = {!!}
