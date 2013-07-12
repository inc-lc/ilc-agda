module Future where

open import Denotational.Notation

-- Uses too much memory.
-- open import Data.Integer

open import Data.Product
open import Data.Sum
open import Data.Unit

postulate ⟦Int⟧ : Set
postulate ⟦Bag⟧ : Set → Set

--mutual
-- First, define a language of types, their denotations, and then the whole algebra of changes in the semantic domain
data Type : Set
⟦_⟧Type : Type → Set

data Type where
  Int : Type
  --Bag : Type → Type
  _⇒_ {- _⊠_ _⊞_ -} : Type → Type → Type
  Δ : (τ : Type) → (old : ⟦ τ ⟧Type) → Type

-- meaningOfType : Meaning Type
-- meaningOfType = meaning ⟦_⟧Type

-- Try out Δ old here

Change : (τ : Type) → ⟦ τ ⟧Type → Set
Change Int old₁ = {!!}
-- Change (Bag τ₁) old₁    = ⟦ Bag τ₁ ⟧Type ⊎ (Σ[ old ∈ (⟦ τ₁ ⟧Type) ] (⟦Bag⟧ ⟦ Δ τ₁ old ⟧Type))
Change (τ₁ ⇒ τ₂) oldF   = ⟦ Δ τ₂ (oldF ?) ⟧Type
-- oldF ? -- oldF ? -- (oldInput : ⟦ τ₁ ⟧Type) → ⟦ Δ τ₁ oldInput ⟧Type → ⟦ Δ τ₂ (oldF oldInput) ⟧Type 
-- Change (τ₁ ⊠ τ₂) old₁ = {!⟦ τ₁ ⟧Type × ⟦ τ₂ ⟧Type!}
-- Change (τ₁ ⊞ τ₂) old₁ = {!!}
Change (Δ τ₁ old₁) old₂ = {!!}

⟦ Int ⟧Type = ⟦Int⟧
-- ⟦ Bag τ ⟧Type = ⟦Bag⟧ ⟦ τ ⟧Type
⟦ σ ⇒ τ ⟧Type = ⟦ σ ⟧Type → ⟦ τ ⟧Type
-- ⟦ σ ⊠ τ ⟧Type = ⟦ σ ⟧Type × ⟦ τ ⟧Type
-- ⟦ σ ⊞ τ ⟧Type = ⟦ σ ⟧Type ⊎ ⟦ τ ⟧Type
⟦ Δ τ old ⟧Type = {- ⊤ ⊎ ⟦ τ ⟧Type ⊎ -} Change τ old
