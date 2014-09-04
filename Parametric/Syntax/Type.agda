------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of function types (Fig. 1a).
------------------------------------------------------------------------

module Parametric.Syntax.Type where

-- This is a module in the Parametric.* hierarchy, so it defines
-- an extension point for plugins. In this case, the plugin can
-- choose the syntax for data types. We always provide a binding
-- called "Structure" that defines the type of the value that has
-- to be provided by the plugin. In this case, the plugin has to
-- provide a type, so we say "Structure = Set".

Structure : Set₁
Structure = Set

-- Here is the parametric module that defines the syntax of
-- simply types in terms of the syntax of base types. In the
-- Parametric.* hierarchy, we always call these parametric
-- modules "Structure". Note that in Agda, there is a separate
-- namespace for module names and for other bindings, so this
-- doesn't clash with the "Structure" above.
--
-- The idea behind all these structures is that the parametric
-- module lifts some structure of the plugin to the corresponding
-- structure in the full language. In this case, we lift the
-- structure of base types to the structure of simple types.
-- Maybe not the best choice of names, but it seemed clever at
-- the time.

module Structure (Base : Structure) where
  infixr 5 _⇒_

  -- A simple type is either a base type or a function types.
  -- Note that we can use our module parameter "Base" here just
  -- like any other type.
  data Type : Set where
    base : (ι : Base) → Type
    _⇒_ : (σ : Type) → (τ : Type) → Type

  -- We also provide the definitions of contexts of the newly
  -- defined simple types, variables as de Bruijn indices
  -- pointing into such a context, and sets of bound variables.
  open import Base.Syntax.Context Type public
  open import Base.Syntax.Vars Type public

  -- Internalize a context to a type.
  --
  -- Is there a better name for this function?
  internalizeContext : (Σ : Context) (τ′ : Type) → Type
  internalizeContext ∅ τ′ = τ′
  internalizeContext (τ • Σ) τ′ = τ ⇒ internalizeContext Σ τ′


  mutual
    --  CBPV
    data ValType : Set where
      U : CompType → ValType
      B : Base → ValType
      Unit : ValType
      _×_ : ValType → ValType → ValType
      _+_ : ValType → ValType → ValType

    data CompType : Set where
      F : ValType → CompType
      _⇛_ : ValType → CompType → CompType
      _Π_ : CompType → CompType → CompType

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

  fromVar : ∀ {Γ τ} → (f : Type → ValType) → Var Γ τ → ValVar (mapValCtx f Γ) (f τ)
  fromVar {x • Γ} f this = vThis
  fromVar {x • Γ} f (that v) = vThat (fromVar f v)
