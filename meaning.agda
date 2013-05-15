module meaning where

open import Level

record Meaning (Syntax : Set) {ℓ : Level} : Set (suc ℓ) where
  constructor
    meaning
  field
    Semantics : Set ℓ
    ⟦_⟧ : Syntax → Semantics

open Meaning {{...}} public

-- smart constructor, making Semantics an implicit argument
newMeaning : ∀ {Syntax ℓ Semantics} → (Syntax → Semantics) → Meaning Syntax {ℓ}
newMeaning {Semantics = Semantics} SemFunction = meaning Semantics SemFunction
