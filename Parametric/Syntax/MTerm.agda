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

module Structure where
  mutual
    -- Analogues of Terms
    Vals : ValContext → ValContext → Set
    Vals Γ = DependentList (Val Γ)

    Comps : ValContext → List CompType → Set
    Comps Γ = DependentList (Comp Γ)

    data Val Γ : (τ : ValType) → Set where
      vVar : ∀ {τ} (x : ValVar Γ τ) → Val Γ τ
      -- XXX Do we need thunks? The draft in the paper doesn't have them.
      vThunk : ∀ {τ} → Comp Γ τ → Val Γ (U τ)

    data Comp Γ : (τ : CompType) → Set where
      -- We probably want different types of constants; some produce values, some produce computations.

      -- Treating all constants as computations is a hack (think of constant values) but they can always be thunked.
      -- Using cbnToCompType is an even bigger hack.
      -- So I add the suffix 'B' for 'Bad'.
      cConstB : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Vals Γ (fromCBNCtx Σ)) →
        Comp Γ (cbnToCompType τ)
      -- So let's try adding another kind of constant for CBV.
      cConstVB : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Vals Γ (fromCBVCtx Σ)) →
        Comp Γ (cbvToCompType τ)
      -- In fact, converting to cConstV c is rather hard.
      -- Let's make the job simpler for now.
      cConstVB2 : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Comps Γ (fromCBVToCompList Σ)) →
        Comp Γ (cbvToCompType τ)
      -- This should be transformed to
      --
      --   arg1 to x1 in (arg2 to x2 in ... (argn to xn in (cConstV c (x1 :: x2 :: ... xn)))).
      --
      -- But it's not trivial to write the recursive functions needed for that. So let's punt for now.

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
  fromCBN : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBNCtx Γ) (cbnToCompType τ)

  fromCBNTerms : ∀ {Γ Σ} → Terms Γ Σ → Vals (fromCBNCtx Γ) (fromCBNCtx Σ)
  --fromCBNTerms ts = DependentList.map (λ t → vThunk (fromCBN t)) ts -- map is not going to work, its type is too stupid.
  fromCBNTerms ∅ = ∅
  fromCBNTerms (px • ts) = vThunk (fromCBN px) • fromCBNTerms ts

  fromCBN (const c args) = cConstB c (fromCBNTerms args)
  fromCBN (var x) = cForce (vVar (fromVar cbnToValType x))
  fromCBN (app s t) = cApp (fromCBN s) (vThunk (fromCBN t))
  fromCBN (abs t) = cAbs (fromCBN t)

  -- To satisfy termination checking, we'd need to inline fromCBV and weaken: fromCBV needs to produce a term in a bigger context.
  -- But let's ignore that.
  {-# NO_TERMINATION_CHECK #-}
  fromCBV : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBVCtx Γ) (cbvToCompType τ)

  {-
  fromCBVTerms : ∀ {Γ Σ} → Terms Γ Σ → Vals (fromCBVCtx Γ) (fromCBVCtx Σ)
  -- use explicit recursion, like for fromCBNTerms.
  fromCBVTerms ∅ = ∅
  fromCBVTerms (px • ts) = {! vThunk (fromCBV px) !} • fromCBVTerms ts
  -- This idea does not work here: in CBV, we can't put thunks into the context. The above code does not typecheck, because the object type has an extra
  -- U (F -)) around it.
  -- That must eliminate F, so it can only use _into_! This algorithm is simply not going to work.
  -- Aaaahh, we just A-normalize the term when converting *const*!
  -}

  cbvTermsToComps : ∀ {Γ Σ} → Terms Γ Σ → Comps (fromCBVCtx Γ) (fromCBVToCompList Σ)
  cbvTermsToComps ∅ = ∅
  cbvTermsToComps (px • ts) = fromCBV px • cbvTermsToComps ts

  {-
  module _ where
    --simpler
    myFold : ∀ {Σ Γ τ} →
      Comps (fromCBVCtx Γ) (fromCBVToCompList Σ) →
      Comp (fromCBVCtx Γ) {!!}
    myFold {∅} ∅ = {!!}
    myFold {x • Σ} (px • cs) = px into {!myFold cs!}

    myFold2 : ∀ {Σ Γ τ} →
      Comps (fromCBVCtx Γ) (fromCBVToCompList Σ) →
      Comp (fromCBVCtx Γ) {!!}
    myFold2 {∅} ∅ = {!!}
    myFold2 {x • Σ} (px • cs) = px into {!myFold cs!}

    open Prefixes

{-
    fromCBVConst' : ∀ {Σ Γ τ} {Σ₁ Σ₂} →
-}

    fromCBVConst' : ∀ {Σ Γ τ} {Σ′ : Prefix Σ} →
      Const Σ τ →
      Comps (fromCBVCtx Γ) (fromCBVToCompList (drop Σ Σ′)) →
      Vals (fromCBVCtx Γ) (fromCBVCtx (take Σ Σ′)) →
      Comp (fromCBVCtx Γ) (cbvToCompType τ)
    fromCBVConst' {∅}     {Σ′ = ∅} c comps vals = cConstV c vals
    fromCBVConst' {x • Σ} {Σ′ = ∅} c comps vals = {!!}
    fromCBVConst' {x • Σ} {Σ′ = .x • Σ′} c comps vals = {!!}
    --fromCBVConst2 c ∅ = cConstV c ∅
    --fromCBVConst2 c (px  ts) = {!px into _!}
      --{!fromCBV px into ?!}
    fromCBVConst3 : ∀ {Γ Σ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
    fromCBVConst3 c ts = fromCBVConst' c (cbvTermsToComps ts) ∅


  fromCBVConst : ∀ {Γ Σ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
  fromCBVConst c ts = cConstV2 c (cbvTermsToComps ts)
  -}

  fromCBV (const c args) = cConstVB2 c (cbvTermsToComps args)
    --fromCBVConst c args
  fromCBV (app s t) =
    (fromCBV s) into
      ((fromCBV (weaken (drop _ • ≼-refl) t)) into
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
