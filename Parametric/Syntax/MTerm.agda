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
ValConstStructure = ValContext → ValType → Set

CompConstStructure : Set₁
CompConstStructure = ValContext → CompType → Set

CbnToCompConstStructure : CompConstStructure → Set
CbnToCompConstStructure CompConst = ∀ {Σ τ} → Const Σ τ → CompConst (fromCBNCtx Σ) (cbnToCompType τ)

CbvToCompConstStructure : CompConstStructure → Set
CbvToCompConstStructure CompConst = ∀ {Σ τ} → Const Σ τ → CompConst (fromCBVCtx Σ) (cbvToCompType τ)

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
      vConst : ∀ {Σ τ} →
        (c : ValConst Σ τ) →
        (args : Vals Γ Σ) →
        Val Γ τ

    data Comp Γ : (τ : CompType) → Set where
      cConst : ∀ {Σ τ} →
        (c : CompConst Σ τ) →
        (args : Vals Γ Σ) →
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

  weaken-vals : ∀ {Γ₁ Γ₂ Σ} →
    (Γ₁≼Γ₂ : Γ₁ ≼≼ Γ₂) →
    Vals Γ₁ Σ →
    Vals Γ₂ Σ

  weaken-val Γ₁≼Γ₂ (vVar x) = vVar (weaken-val-var Γ₁≼Γ₂ x)
  weaken-val Γ₁≼Γ₂ (vThunk x) = vThunk (weaken-comp Γ₁≼Γ₂ x)
  weaken-val Γ₁≼Γ₂ (vConst c args) = vConst c (weaken-vals Γ₁≼Γ₂ args)
  weaken-comp Γ₁≼Γ₂ (cConst c args) = cConst c (weaken-vals Γ₁≼Γ₂ args)
  weaken-comp Γ₁≼Γ₂ (cForce x) = cForce (weaken-val Γ₁≼Γ₂ x)
  weaken-comp Γ₁≼Γ₂ (cReturn v) = cReturn (weaken-val Γ₁≼Γ₂ v)
  weaken-comp Γ₁≼Γ₂ (_into_ {σ} c c₁) = (weaken-comp Γ₁≼Γ₂ c) into (weaken-comp (keep σ •• Γ₁≼Γ₂) c₁)
  weaken-comp Γ₁≼Γ₂ (cAbs {σ} c) = cAbs (weaken-comp (keep σ •• Γ₁≼Γ₂) c)
  weaken-comp Γ₁≼Γ₂ (cApp s t) = cApp (weaken-comp Γ₁≼Γ₂ s) (weaken-val Γ₁≼Γ₂ t)

  weaken-vals Γ₁≼Γ₂ ∅ = ∅
  weaken-vals Γ₁≼Γ₂ (px • ts) = (weaken-val Γ₁≼Γ₂ px) • (weaken-vals Γ₁≼Γ₂ ts)

  fromCBN : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBNCtx Γ) (cbnToCompType τ)

  fromCBNTerms : ∀ {Γ Σ} → Terms Γ Σ → Vals (fromCBNCtx Γ) (fromCBNCtx Σ)
  fromCBNTerms ∅ = ∅
  fromCBNTerms (px • ts) = vThunk (fromCBN px) • fromCBNTerms ts

  fromCBN (const c args) = cConst (cbnToCompConst c) (fromCBNTerms args)
  fromCBN (var x) = cForce (vVar (fromVar cbnToValType x))
  fromCBN (app s t) = cApp (fromCBN s) (vThunk (fromCBN t))
  fromCBN (abs t) = cAbs (fromCBN t)

  -- To satisfy termination checking, we'd need to inline fromCBV and weaken: fromCBV needs to produce a term in a bigger context.
  -- But let's ignore that.
  {-# TERMINATING #-}
  fromCBV : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBVCtx Γ) (cbvToCompType τ)

  cbvTermsToComps : ∀ {Γ Σ} → Terms Γ Σ → Comps (fromCBVCtx Γ) (fromCBVToCompList Σ)
  cbvTermsToComps ∅ = ∅
  cbvTermsToComps (px • ts) = fromCBV px • cbvTermsToComps ts


  dequeValContexts : ValContext → ValContext → ValContext
  dequeValContexts ∅ Γ = Γ
  dequeValContexts (x • Σ) Γ = dequeValContexts Σ (x • Γ)

  dequeValContexts≼≼ : ∀ Σ Γ → Γ ≼≼ dequeValContexts Σ Γ
  dequeValContexts≼≼ ∅ Γ = ≼≼-refl
  dequeValContexts≼≼ (x • Σ) Γ = ≼≼-trans (drop_••_ x ≼≼-refl) (dequeValContexts≼≼ Σ (x • Γ))

  dequeContexts : Context → Context → ValContext
  dequeContexts Σ Γ = dequeValContexts (fromCBVCtx Σ) (fromCBVCtx Γ)

  fromCBVArg :
    ∀ {σ Γ τ} → Term Γ τ →
      (Val (cbvToValType τ • fromCBVCtx Γ) (cbvToValType τ) →
        Comp (cbvToValType τ • fromCBVCtx Γ) (cbvToCompType σ)) →
      Comp (fromCBVCtx Γ) (cbvToCompType σ)
  fromCBVArg t k =
    (fromCBV t) into
      k (vVar vThis)

  fromCBVArgs :
    ∀ {Σ Γ τ} → Terms Γ Σ →
      (Vals (dequeContexts Σ Γ) (fromCBVCtx Σ) →
        Comp (dequeContexts Σ Γ) (cbvToCompType τ)) →
      Comp (fromCBVCtx Γ) (cbvToCompType τ)
  fromCBVArgs ∅ k = k ∅
  fromCBVArgs {σ • Σ} {Γ} (t • ts) k =
    fromCBVArg t (λ v →
      fromCBVArgs
        (weaken-terms (drop_•_ _ ≼-refl) ts) (λ vs →
          k (weaken-val (dequeValContexts≼≼ (fromCBVCtx Σ) _) v • vs)))

  -- Transform a constant application into
  --
  --   arg1 to x1 in (arg2 to x2 in ... (argn to xn in (cConst (cbvToCompConst c) (x1 :: x2 :: ... xn)))).

  fromCBVConstCPSRoot : ∀ {Σ Γ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
  fromCBVConstCPSRoot c ts = fromCBVArgs ts (cConst (cbvToCompConst c))

  fromCBV (const c args) = fromCBVConstCPSRoot c args
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
