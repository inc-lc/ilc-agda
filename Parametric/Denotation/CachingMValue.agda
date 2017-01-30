------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Values for caching evaluation of MTerm
------------------------------------------------------------------------
import Parametric.Syntax.Type as Type
import Parametric.Syntax.MType as MType

import Parametric.Denotation.Value as Value
import Parametric.Denotation.MValue as MValue

module Parametric.Denotation.CachingMValue
    (Base : Type.Structure)
    (⟦_⟧Base : Value.Structure Base)
  where

open import Base.Data.DependentList
open import Base.Denotation.Notation

open Type.Structure Base
open MType.Structure Base
open Value.Structure Base ⟦_⟧Base
open MValue.Structure Base ⟦_⟧Base

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Level
open import Function hiding (const)

Structure : Set
Structure = Base Type → Type

module Structure (ΔBase : Structure) where
  {-# TERMINATING #-}
  ⟦_⟧ValTypeHidCache : (τ : ValType) → Set
  ⟦_⟧CompTypeHidCache : (τ : CompType) → Set

  ⟦ U c ⟧ValTypeHidCache = ⟦ c ⟧CompTypeHidCache
  ⟦ B ι ⟧ValTypeHidCache = ⟦ base ι ⟧
  ⟦ vUnit ⟧ValTypeHidCache = ⊤
  ⟦ τ₁ v× τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache × ⟦ τ₂ ⟧ValTypeHidCache
  ⟦ τ₁ v+ τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache ⊎ ⟦ τ₂ ⟧ValTypeHidCache

  --
  -- XXX The termination checker isn't happy with it, and it may be right ─ if
  -- you keep substituting τ₁ = U (F τ), you can make the cache arbitrarily big.
  -- I think we don't do that unless we are caching a non-terminating
  -- computation to begin with, but I'm not entirely sure.
  --
  -- However, the termination checker can't prove that the function is
  -- terminating because it's not structurally recursive, but one call of the
  -- function will produce another call of the function stuck on a neutral term:
  -- So the computation will have terminated, just in an unusual way!
  --
  -- Anyway, I need not mechanize this part of the proof for my goals.
  --
  -- XXX: This line is the only change, up to now, for the caching semantics,
  -- the rest is copied. Inheritance would handle this precisely; without
  -- inheritance, we might want to use one of the standard encodings of related
  -- features (delegation?).
  ⟦ F τ ⟧CompTypeHidCache = (Σ[ τ₁ ∈ ValType ] ⟦ τ ⟧ValTypeHidCache × ⟦ τ₁ ⟧ValTypeHidCache )
  ⟦ σ ⇛ τ ⟧CompTypeHidCache = ⟦ σ ⟧ValTypeHidCache → ⟦ τ ⟧CompTypeHidCache

  ⟦_⟧ValCtxHidCache : (Γ : ValContext) → Set
  ⟦_⟧ValCtxHidCache = DependentList ⟦_⟧ValTypeHidCache

  {-# TERMINATING #-}
  ⟦_⟧ΔValType : ValType → Set
  ⟦_⟧ΔCompType : CompType → Set
  ⟦_⟧ΔCompType (F τ) = Σ[ τ₁ ∈ ValType ] (⟦ τ₁ ⟧ValTypeHidCache → ⟦ τ ⟧ΔValType × ⟦ τ₁ ⟧ValTypeHidCache)
  ⟦_⟧ΔCompType (σ ⇛ τ) = ⟦ σ ⟧ΔValType → ⟦ τ ⟧ΔCompType

  ⟦_⟧ΔValType (U c) = ⟦ c ⟧ΔCompType
  ⟦_⟧ΔValType (B ι) = ⟦ ΔBase ι ⟧
  ⟦_⟧ΔValType vUnit = ⊤
  ⟦_⟧ΔValType (τ₁ v× τ₂) = ⟦_⟧ΔValType τ₁ × ⟦_⟧ΔValType τ₂
  ⟦_⟧ΔValType (τ₁ v+ τ₂) = (⟦_⟧ΔValType τ₁ ⊎ ⟦_⟧ΔValType τ₂) ⊎ (⟦ τ₁ ⟧ ⊎ ⟦ τ₂ ⟧)

open import Data.Product
open import Level

-- -- Needed to allow storing functions in cache:
-- record _↝_↝_ {a b} (S : Set a) c (T : Set b) : Set (a ⊔ b ⊔ suc c) where
--   field
--     cache : Set c
--     fun : S → (T × cache)

-- record _↝′_↝′_ {a b} (dS : Set a) c (dT : Set b) : Set (a ⊔ b ⊔ suc c) where
--   field
--     cache : Set c
--     fun : dS → cache → (dT × cache)

-- -- -- For simplicity, but won't work:
-- --
-- -- record _↝_ {a b} (S : Set a) (T : Set b) : Set (a ⊔ b ⊔ suc zero) where
-- --   field
-- --     cache : Set
-- --     fun : S → (T × cache)
-- -- record _↝′_ (da : Set₁) (db : Set₁) : Set₁ where
-- --   field
-- --     cache : Set
-- --     dfun : da → cache → (db × cache)

-- fooo : (a b : Set₁) → Set₁
-- fooo a b = a ↝ zero ↝ (b ↝ zero ↝ b)

-- dfooo : (da db : Set₁) → Set₁
-- dfooo da db = da ↝′ zero ↝′ (db ↝′ zero ↝′ db)

-- Since caches can contain caches, including function caches, we can't use the
-- above. The existentials must store object-language codes of some sort. For
-- extra fun, the resulting code is not typeable with simple types, so we can't
-- use codes for simple types but must store, say, function bodies.
