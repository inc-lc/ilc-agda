import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Syntax.MType as MType

module Parametric.Syntax.MTerm
    {Base : Type.Structure}
    (Const : Term.Structure Base)
  where

open Type.Structure Base
open MType.Structure Base
open Term.Structure Base Const

-- Our extension points are sets of primitives, indexed by the
-- types of their arguments and their return type.

-- We want different types of constants; some produce values, some produce
-- computations. In all cases, arguments are assumed to be values (though
-- individual primitives might require thunks).

ValConstStructure : Set₁
ValConstStructure = ValType → Set

CompConstStructure : Set₁
CompConstStructure = CompType → Set

CbnToCompConstStructure : CompConstStructure → Set
CbnToCompConstStructure CompConst = ∀ {τ} → Const τ → CompConst (cbnToCompType τ)

CbvToCompConstStructure : CompConstStructure → Set
CbvToCompConstStructure CompConst = ∀ {τ} → Const τ → CompConst (cbvToCompType τ)

module
  Structure
    (ValConst : ValConstStructure) (CompConst : CompConstStructure)
    (cbnToCompConst : CbnToCompConstStructure CompConst)
    (cbvToCompConst : CbvToCompConstStructure CompConst) where
  mutual
    -- Analogues of Terms
    Vals : ValContext → ValContext → Set
    Vals Γ = DependentList (Val Γ)

    Comps : ValContext → List CompType → Set
    Comps Γ = DependentList (Comp Γ)

    data Val Γ : (τ : ValType) → Set where
      vVar : ∀ {τ} (x : ValVar Γ τ) → Val Γ τ
      -- XXX Do we need thunks? The draft in the paper doesn't have them.
      -- However, they will start being useful if we deal with CBN source
      -- languages.
      vThunk : ∀ {τ} → Comp Γ τ → Val Γ (U τ)
      vConst : ∀ {τ} →
        (c : ValConst τ) →
        Val Γ τ

    data Comp Γ : (τ : CompType) → Set where
      cConst : ∀ {τ} →
        (c : CompConst τ) →
        Comp Γ τ

      cForce : ∀ {τ} → Val Γ (U τ) → Comp Γ τ
      cReturn : ∀ {τ} (v : Val Γ τ) → Comp Γ (F τ)
      {-
      -- Originally, M to x in N. But here we have no names!
      _into_ : ∀ {σ τ} →
        (e₁ : Comp Γ (F σ)) →
        (e₂ : Comp (σ •• Γ) τ) →
        Comp Γ τ
      -}
      -- The following constructor is the main difference between CBPV and this
      -- monadic calculus. This is better for the caching transformation.
      _into_ : ∀ {σ τ} →
        (e₁ : Comp Γ (F σ)) →
        (e₂ : Comp (σ •• Γ) (F τ)) →
        Comp Γ (F τ)
      cAbs : ∀ {σ τ} →
        (t : Comp (σ •• Γ) τ) →
        Comp Γ (σ ⇛ τ)
      cApp : ∀ {σ τ} →
        (s : Comp Γ (σ ⇛ τ)) →
        (t : Val Γ σ) →
        Comp Γ τ

  weaken-val : ∀ {Γ₁ Γ₂ τ} →
    (Γ₁≼Γ₂ : Γ₁ ≼≼ Γ₂) →
    Val Γ₁ τ →
    Val Γ₂ τ

  weaken-comp : ∀ {Γ₁ Γ₂ τ} →
    (Γ₁≼Γ₂ : Γ₁ ≼≼ Γ₂) →
    Comp Γ₁ τ →
    Comp Γ₂ τ

  weaken-val Γ₁≼Γ₂ (vVar x) = vVar (weaken-val-var Γ₁≼Γ₂ x)
  weaken-val Γ₁≼Γ₂ (vThunk x) = vThunk (weaken-comp Γ₁≼Γ₂ x)
  weaken-val Γ₁≼Γ₂ (vConst c) = vConst c
  weaken-comp Γ₁≼Γ₂ (cConst c) = cConst c
  weaken-comp Γ₁≼Γ₂ (cForce x) = cForce (weaken-val Γ₁≼Γ₂ x)
  weaken-comp Γ₁≼Γ₂ (cReturn v) = cReturn (weaken-val Γ₁≼Γ₂ v)
  weaken-comp Γ₁≼Γ₂ (_into_ {σ} c c₁) = (weaken-comp Γ₁≼Γ₂ c) into (weaken-comp (keep σ •• Γ₁≼Γ₂) c₁)
  weaken-comp Γ₁≼Γ₂ (cAbs {σ} c) = cAbs (weaken-comp (keep σ •• Γ₁≼Γ₂) c)
  weaken-comp Γ₁≼Γ₂ (cApp s t) = cApp (weaken-comp Γ₁≼Γ₂ s) (weaken-val Γ₁≼Γ₂ t)

  fromCBN : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBNCtx Γ) (cbnToCompType τ)
  fromCBN (const c) = cConst (cbnToCompConst c)
  fromCBN (var x) = cForce (vVar (fromVar cbnToValType x))
  fromCBN (app s t) = cApp (fromCBN s) (vThunk (fromCBN t))
  fromCBN (abs t) = cAbs (fromCBN t)

  -- To satisfy termination checking, we'd need to inline fromCBV and weaken: fromCBV needs to produce a term in a bigger context.
  -- But let's ignore that.
  {-# TERMINATING #-}
  fromCBV : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBVCtx Γ) (cbvToCompType τ)

  fromCBV (const c) = cConst (cbvToCompConst c)
  fromCBV (app s t) =
    (fromCBV s) into
      (fromCBV (weaken (drop _ • ≼-refl) t) into
        cApp (cForce (vVar (vThat vThis))) (vVar vThis))
  -- Values
  fromCBV (var x) = cReturn (vVar (fromVar cbvToValType x))
  fromCBV (abs t) = cReturn (vThunk (cAbs (fromCBV t)))

  -- This reflects the CBV conversion of values in TLCA '99, but we can't write
  -- this because it's partial on the Term type. Instead, we duplicate thunking
  -- at the call site.
  {-
  fromCBVToVal : ∀ {Γ τ} (t : Term Γ τ) → Val (fromCBVCtx Γ) (cbvToValType τ)
  fromCBVToVal (var x) = vVar (fromVar cbvToValType x)
  fromCBVToVal (abs t) = vThunk (cAbs (fromCBV t))

  fromCBVToVal (const c args) = {!!}
  fromCBVToVal (app t t₁) = {!!} -- Not a value
  -}
