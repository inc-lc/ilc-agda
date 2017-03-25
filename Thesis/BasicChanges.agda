module Thesis.BasicChanges where

open import Thesis.Lang
open import Data.Empty
open import Relation.Binary.PropositionalEquality

-- L stands for "Language", because these structures are defined over the syntax
-- of _language_ types, as opposed to being defined over arbitrary sets.
module _ (τ₁ τ₂ : Type) where
  data LSumChange2 : Set where
    ch₁ : (da : Chτ τ₁) → LSumChange2
    ch₂ : (db : Chτ τ₂) → LSumChange2
    rp : (s : ⟦ sum τ₁ τ₂ ⟧Type) → LSumChange2
  LSumChange = (Chτ τ₁ ⊎ Chτ τ₂) ⊎ ⟦ sum τ₁ τ₂ ⟧Type

module _ {τ₁ τ₂ : Type} where
  lConvert : LSumChange τ₁ τ₂ → LSumChange2 τ₁ τ₂
  lConvert (inj₁ (inj₁ da)) = ch₁ da
  lConvert (inj₁ (inj₂ db)) = ch₂ db
  lConvert (inj₂ s) = rp s
  lConvert₁ : LSumChange2 τ₁ τ₂ → LSumChange τ₁ τ₂
  lConvert₁ (ch₁ da) = inj₁ (inj₁ da)
  lConvert₁ (ch₂ db) = inj₁ (inj₂ db)
  lConvert₁ (rp s) = inj₂ s

[_]τ_from_to_ : ∀ (τ : Type) → (dv : Chτ τ) → (v1 v2 : ⟦ τ ⟧Type) → Set

-- This can't be a datatype, since it wouldn't be strictly positive as it
-- appears on the left of an arrow in the function case, which then can be
-- contained in nested "fromto-validity" proofs.
sumfromto : ∀ (σ τ : Type) → (dv : LSumChange2 σ τ) → (v1 v2 : ⟦ sum σ τ ⟧Type) → Set
sumfromto σ τ (ch₁ da) (inj₁ a1) (inj₁ a2) = [ σ ]τ da from a1 to a2
-- These fallback equations unfortunately don't hold definitionally, they're
-- split on multiple cases, so the pattern match is a mess.
--
-- To "case split" on validity, I typically copy-paste the pattern match from
-- fromto→⊕ and change the function name :-(.
sumfromto σ τ (ch₁ da) _ _ = ⊥
sumfromto σ τ (ch₂ db) (inj₂ b1) (inj₂ b2) = [ τ ]τ db from b1 to b2
sumfromto σ τ (ch₂ db) _ _ = ⊥
sumfromto σ τ (rp (inj₂ b2)) (inj₁ a1) (inj₂ b2') = b2 ≡ b2'
sumfromto σ τ (rp (inj₁ a2)) (inj₂ b1) (inj₁ a2') = a2 ≡ a2'
sumfromto σ τ (rp s) _ _ = ⊥

[ σ ⇒ τ ]τ df from f1 to f2 =
  ∀ (da : Chτ σ) (a1 a2 : ⟦ σ ⟧Type) →
  [ σ ]τ da from a1 to a2 → [ τ ]τ df a1 da from f1 a1 to f2 a2
[ int ]τ dv from v1 to v2 = v1 + dv ≡ v2
[ pair σ τ ]τ (da , db) from (a1 , b1) to (a2 , b2) = [ σ ]τ da from a1 to a2 × [ τ ]τ db from b1 to b2
[ sum σ τ ]τ dv from v1 to v2 = sumfromto σ τ (lConvert dv) v1 v2

data [_]Γ_from_to_ : ∀ Γ → ChΓ Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set where
  v∅ : [ ∅ ]Γ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Γ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ]τ dv from v1 to v2) →
    (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
    [ τ • Γ ]Γ (dv • v1 • dρ) from (v1 • ρ1) to (v2 • ρ2)

-- record BasicChangeStructure (A : Set) : Set₁ where
--   field
--     Ch : Set
--     ch_from_to_ : (dv : Ch) → (v1 v2 : A) → Set

-- BCh : ∀ (A : Set) → {{CA : BasicChangeStructure A}} → Set
-- BCh A {{CA}} = BasicChangeStructure.Ch CA

-- basicChangeStructureτ : ∀ τ → BasicChangeStructure ⟦ τ ⟧Type
-- basicChangeStructureτ τ = record
--   { Ch = Chτ τ
--   ; ch_from_to_ = [ τ ]τ_from_to_
--   }

-- basicChangeStructureΓ : ∀ Γ → BasicChangeStructure ⟦ Γ ⟧Context
-- basicChangeStructureΓ Γ = record
--   { Ch = ChΓ Γ
--   ; ch_from_to_ = [ Γ ]Γ_from_to_
--   }

-- instance{}
--   ibasicChangeStructureτ : ∀ {τ} → BasicChangeStructure ⟦ τ ⟧Type
--   ibasicChangeStructureτ {τ} = basicChangeStructureτ τ

--   ibasicChangeStructureΓ : ∀ {Γ} → BasicChangeStructure ⟦ Γ ⟧Context
--   ibasicChangeStructureΓ {Γ} = basicChangeStructureΓ Γ
