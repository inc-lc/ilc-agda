module Postulate.Extensionality where

-- POSTULATE EXTENSIONALITY
--
-- Justification on Agda mailing list:
-- http://permalink.gmane.org/gmane.comp.lang.agda/2343

open import Relation.Binary.PropositionalEquality

postulate ext : ∀ {a b} → Extensionality a b

-- Convenience of using extensionality 3 times in a row
-- (using it twice in a row is moderately tolerable)
ext³ : ∀
  {A : Set}
  {B : A → Set}
  {C : (a : A) → B a → Set }
  {D : (a : A) → (b : B a) → C a b → Set}
  {f g : (a : A) → (b : B a) → (c : C a b) → D a b c} →
  ((a : A) (b : B a) (c : C a b) → f a b c ≡ g a b c) → f ≡ g

ext³ fabc=gabc = ext (λ a → ext (λ b → ext (λ c → fabc=gabc a b c)))
