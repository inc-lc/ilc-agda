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

module Structure where
  {-# NO_TERMINATION_CHECK #-}
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

  {-
  ⟦_⟧CompCtxHidCache : (Γ : CompContext) → Set₁
  ⟦_⟧CompCtxHidCache = DependentList ⟦_⟧CompTypeHidCache
  -}
