import Parametric.Syntax.Type as Type

module Parametric.Syntax.MType where

module Structure (Base : Type.Structure) where
  open Type.Structure Base

  mutual
    --  Derived from CBPV
    data ValType : Set where
      U : (c : CompType) → ValType
      B : (ι : Base) → ValType
      vUnit : ValType
      _v×_ : (τ₁ : ValType) → (τ₂ : ValType) → ValType
      _v+_ : (τ₁ : ValType) → (τ₂ : ValType) → ValType

    data CompType : Set where
      F : ValType → CompType
      _⇛_ : ValType → CompType → CompType
      -- We did not use this in CBPV, so dropped.
      -- _Π_ : CompType → CompType → CompType

  cbnToCompType : Type → CompType
  cbnToCompType (base ι) = F (B ι)
  cbnToCompType (σ ⇒ τ) = U (cbnToCompType σ) ⇛ cbnToCompType τ

  cbvToValType : Type → ValType
  cbvToValType (base ι) = B ι
  cbvToValType (σ ⇒ τ) = U (cbvToValType σ ⇛ F (cbvToValType τ))

  open import Base.Syntax.Context ValType public
    using ()
    renaming
      ( ∅ to ∅∅
      ; _•_ to _••_
      ; mapContext to mapValCtx
      ; Var to ValVar
      ; Context to ValContext
      ; this to vThis; that to vThat)

  cbnToValType : Type → ValType
  cbnToValType τ = U (cbnToCompType τ)

  cbvToCompType : Type → CompType
  cbvToCompType τ = F (cbvToValType τ)

  fromCBNCtx : Context → ValContext
  fromCBNCtx Γ = mapValCtx cbnToValType Γ

  fromCBVCtx : Context → ValContext
  fromCBVCtx Γ = mapValCtx cbvToValType Γ

  open import Data.List
  open Data.List using (List) public
  fromCBVToCompList : Context → List CompType
  fromCBVToCompList Γ = mapValCtx cbvToCompType Γ

  fromVar : ∀ {Γ τ} → (f : Type → ValType) → Var Γ τ → ValVar (mapValCtx f Γ) (f τ)
  fromVar {x • Γ} f this = vThis
  fromVar {x • Γ} f (that v) = vThat (fromVar f v)
