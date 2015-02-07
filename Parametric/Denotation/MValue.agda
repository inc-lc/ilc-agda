------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Values for standard evaluation of MTerm
------------------------------------------------------------------------
import Parametric.Syntax.Type as Type
import Parametric.Syntax.MType as MType
import Parametric.Denotation.Value as Value

module Parametric.Denotation.MValue
    (Base : Type.Structure)
    (⟦_⟧Base : Value.Structure Base)
  where

open import Base.Denotation.Notation

open Type.Structure Base
open MType.Structure Base
open Value.Structure Base ⟦_⟧Base

open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit
open import Level
open import Function hiding (const)

module Structure where

  -- Defining a caching semantics for Term proves to be hard, requiring to
  -- insert and remove caches where we apply constants.

  -- Indeed, our plugin interface is not satisfactory for adding caching. CBPV can help us.

  ⟦_⟧ValType : (τ : ValType) → Set
  ⟦_⟧CompType : (τ : CompType) → Set

  ⟦ U c ⟧ValType = ⟦ c ⟧CompType
  ⟦ B ι ⟧ValType = ⟦ base ι ⟧
  ⟦ vUnit ⟧ValType = ⊤
  ⟦ τ₁ v× τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType × ⟦ τ₂ ⟧ValType
  ⟦ τ₁ v+ τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType ⊎ ⟦ τ₂ ⟧ValType

  ⟦ F τ ⟧CompType = ⟦ τ ⟧ValType
  ⟦ σ ⇛ τ ⟧CompType = ⟦ σ ⟧ValType → ⟦ τ ⟧CompType

  -- This means: Overload ⟦_⟧ to mean ⟦_⟧ValType.
  meaningOfValType : Meaning ValType
  meaningOfValType = meaning ⟦_⟧ValType

  meaningOfCompType : Meaning CompType
  meaningOfCompType = meaning ⟦_⟧CompType

  -- We also provide: Environments of values (but not of computations).
  open import Base.Denotation.Environment ValType ⟦_⟧ValType public
    using ()
    renaming ( ⟦_⟧Var to ⟦_⟧ValVar
             ; ⟦_⟧Context to ⟦_⟧ValContext
             ; meaningOfContext to meaningOfValContext
             )
