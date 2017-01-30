------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Logical relation for erasure with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Implementation where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation
open import Nehemiah.Change.Validity
open import Nehemiah.Change.Type
open import Nehemiah.Change.Value
open import Nehemiah.Change.Derive

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Nehemiah

open import Base.Change.Equivalence
open import Base.Change.Products using (doe-respect-projs)
import Parametric.Change.Implementation
    Const ⟦_⟧Base ⟦_⟧Const ΔBase
    ⟦apply-base⟧ ⟦diff-base⟧ ⟦nil-base⟧ derive-const as Implementation

private
  {-# TERMINATING #-}
  implements-base : ∀ ι {v : ⟦ ι ⟧Base} → Δ₍ ι ₎ v → ⟦ ΔBase ι ⟧Type → Set
  u⊟v≈u⊝v-base : ∀ ι → {u v : ⟦ ι ⟧Base} →
      implements-base ι {v} (u ⊟₍ ι ₎ v) (⟦diff-base⟧ ι u v)
  nil-v≈⟦nil⟧-v-base : ∀ ι {v : ⟦ ι ⟧Base} →
    implements-base ι (nil₍ ι ₎ v) (⟦nil-base⟧ ι v)
  carry-over-base : ∀ {ι}
    {v : ⟦ ι ⟧Base}
    (Δv : Δ₍ ι ₎ v)
    {Δv′ : ⟦ ΔBase ι ⟧Type} (Δv≈Δv′ : implements-base ι {v} Δv Δv′) →
      v ⊞₍ base ι ₎ Δv ≡ v ⟦⊕₍ base ι ₎⟧ Δv′
  implements-base-respects-doe : ∀ ι
    {v : ⟦ ι ⟧Base} {Δv₁ Δv₂ : Δ₍ ι ₎ v}
    (Δv₁≙Δv₂ : _≙_ {{change-algebra₍_₎ {P = ⟦_⟧Base} ι}} Δv₁ Δv₂) →
    {Δv′ : ⟦ ΔBase ι ⟧} (Δv₁≈Δv′ : implements-base ι {v} Δv₁ Δv′) →
    implements-base ι Δv₂ Δv′


implementation-structure : Implementation.Structure
implementation-structure = record
    { implements-base = implements-base
    ; implements-base-respects-doe = implements-base-respects-doe
    ; u⊟v≈u⊝v-base = u⊟v≈u⊝v-base
    ; nil-v≈⟦nil⟧-v-base = nil-v≈⟦nil⟧-v-base
    ; carry-over-base = carry-over-base
    }

module R = Implementation.Structure implementation-structure

implements-base base-int {v} Δv Δv′ = Δv ≡ Δv′
implements-base base-bag {v} Δv Δv′ = Δv ≡ Δv′
implements-base (base-pair τ₁ τ₂) {v₁ , v₂} (Δv₁ , Δv₂) (Δv′₁ , Δv′₂) = R.implements τ₁ Δv₁ Δv′₁ × R.implements τ₂ Δv₂ Δv′₂

open import Theorem.Groups-Nehemiah
open ≡-Reasoning
implements-base-respects-doe base-int {v} {Δv₁} {Δv₂} (doe v+Δv₁≡v+Δv₂) refl =
  begin
    Δv₂
  ≡⟨ sym ([m+n]-m=n {v} {Δv₂}) ⟩
    (v + Δv₂) - v
  ≡⟨ cong (_- v) (sym v+Δv₁≡v+Δv₂) ⟩
    (v + Δv₁) - v
  ≡⟨ [m+n]-m=n {v} {Δv₁} ⟩
    Δv₁
  ∎

implements-base-respects-doe base-bag {v} {Δv₁} {Δv₂} (doe proof₁) refl =
  begin
    Δv₂
  ≡⟨ sym [a++b]\\a=b ⟩
    (v ++ Δv₂) \\ v
  ≡⟨ cong (_\\ v) (sym proof₁) ⟩
    (v ++ Δv₁) \\ v
  ≡⟨ [a++b]\\a=b ⟩
    Δv₁
  ∎

implements-base-respects-doe (base-pair τ₁ τ₂)
  {v = v₁ , v₂} Δv₁≙Δv₂ (Δv₁≈Δv′₁ , Δv₁≈Δv′₂) =
    R.implements-respects-doe τ₁ (proj₁ (doe-respect-projs {{CA = change-algebra₍ τ₁ ₎}} {{CB = change-algebra₍ τ₂ ₎ }} Δv₁≙Δv₂)) Δv₁≈Δv′₁
  , R.implements-respects-doe τ₂ (proj₂ (doe-respect-projs {{CA = change-algebra₍ τ₁ ₎}} {{CB = change-algebra₍ τ₂ ₎ }} Δv₁≙Δv₂)) Δv₁≈Δv′₂

u⊟v≈u⊝v-base base-int = refl
u⊟v≈u⊝v-base base-bag = refl
u⊟v≈u⊝v-base (base-pair τ₁ τ₂) {u₁ , u₂} {v₁ , v₂}= R.u⊟v≈u⊝v {τ₁} , R.u⊟v≈u⊝v {τ₂}

nil-v≈⟦nil⟧-v-base base-int = refl
nil-v≈⟦nil⟧-v-base base-bag = refl
nil-v≈⟦nil⟧-v-base (base-pair τ₁ τ₂) {v₁ , v₂} = R.nil-v≈⟦nil⟧-v {τ₁},  R.nil-v≈⟦nil⟧-v {τ₂}

carry-over-base {base-int} {v} Δv Δv≈Δv′ = cong (_+_ v) Δv≈Δv′
carry-over-base {base-bag} Δv Δv≈Δv′ = cong (_++_ (before₍ bag ₎ Δv)) Δv≈Δv′
carry-over-base {base-pair τ₁ τ₂}  {v₁ , v₂} (Δv₁ , Δv₂) {Δv′₁ , Δv′₂} (Δv≈Δv′₁ , Δv≈Δv′₂) = cong₂ _,_ (R.carry-over {τ₁} Δv₁ Δv≈Δv′₁) (R.carry-over {τ₂} Δv₂ Δv≈Δv′₂)

open R public
