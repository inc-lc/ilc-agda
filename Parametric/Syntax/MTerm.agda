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

module Structure (ValConst : ValConstStructure) (CompConst : CompConstStructure) where
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

      {-
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
      -}
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
  --fromCBNTerms ts = DependentList.map (λ t → vThunk (fromCBN t)) ts -- map is not going to work, its type is too stupid.
  fromCBNTerms ∅ = ∅
  fromCBNTerms (px • ts) = vThunk (fromCBN px) • fromCBNTerms ts

  open import UNDEFINED
  -- This is really supposed to be part of the plugin interface.
  cbnToCompConst : ∀ {Σ τ} → Const Σ τ → CompConst (fromCBNCtx Σ) (cbnToCompType τ)
  cbnToCompConst = reveal UNDEFINED

  fromCBN (const c args) = cConst (cbnToCompConst c) (fromCBNTerms args) -- cConstB c (fromCBNTerms args)
  fromCBN (var x) = cForce (vVar (fromVar cbnToValType x))
  fromCBN (app s t) = cApp (fromCBN s) (vThunk (fromCBN t))
  fromCBN (abs t) = cAbs (fromCBN t)

  -- To satisfy termination checking, we'd need to inline fromCBV and weaken: fromCBV needs to produce a term in a bigger context.
  -- But let's ignore that.
  {-# NO_TERMINATION_CHECK #-}
  fromCBV : ∀ {Γ τ} (t : Term Γ τ) → Comp (fromCBVCtx Γ) (cbvToCompType τ)

  -- This is really supposed to be part of the plugin interface.
  cbvToCompConst : ∀ {Σ τ} → Const Σ τ → CompConst (fromCBVCtx Σ) (cbvToCompType τ)
  cbvToCompConst = reveal UNDEFINED

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

  module _ where
  {-
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


{-
    fromCBVConst' : ∀ {Σ Γ τ} {Σ₁ Σ₂} →
-}

    fromCBVConst'' : ∀ {Σ Σ′ Γ τ} →
      Const Σ τ →
      Comps (fromCBVCtx Γ) (fromCBVToCompList Σ′) →
      Vals (fromCBVCtx Γ) (fromCBVCtx ) →
      Comp (fromCBVCtx Γ) (cbvToCompType τ)
-}

    open Prefixes
    {-
    fromCBVConst' : ∀ {Σ Γ τ} {Σ′ : Prefix Σ} →
      Const Σ τ →
      Comps (fromCBVCtx Γ) (fromCBVToCompList (drop Σ Σ′)) →
      Vals (fromCBVCtx Γ) (fromCBVCtx (take Σ Σ′)) →
      Comp (fromCBVCtx Γ) (cbvToCompType τ)
    fromCBVConst' {∅}     {Σ′ = ∅} c comps vals = cConst (cbvToCompConst c) vals --cConstV c vals
    fromCBVConst' {x • Σ} c comps vals = {!!}

--    fromCBVConst' {x • Σ} {Σ′ = ∅} c (px • comps) ∅ = {!!} -- px into (fromCBVConst' {c {! comps!} {!!})
-- cConst (cbvToCompConst c) {!!}
--    fromCBVConst' {x • Σ} {Σ′ = .x • Σ′} c comps vals = {!!} -- px into (fromCBVConst' c ? ?)
    --cConst (cbvToCompConst c) {!!}
    --fromCBVConst2 c ∅ = cConstV c ∅
    --fromCBVConst2 c (px  ts) = {!px into _!}
      --{!fromCBV px into ?!}
    fromCBVConst3 : ∀ {Γ Σ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
    fromCBVConst3 c ts = fromCBVConst' c (cbvTermsToComps ts) ∅
    -}
    dequeValContexts : ValContext → ValContext → ValContext
    dequeValContexts ∅ Γ = Γ
    dequeValContexts (x • Σ) Γ = dequeValContexts Σ (x • Γ)

    dequeValContexts≼≼ : ∀ Σ Γ → Γ ≼≼ dequeValContexts Σ Γ
    dequeValContexts≼≼ ∅ Γ = ≼≼-refl
    dequeValContexts≼≼ (x • Σ) Γ = ≼≼-trans (drop_••_ x ≼≼-refl) (dequeValContexts≼≼ Σ (x • Γ)) --

    dequeContexts : Context → Context → ValContext
    dequeContexts Σ Γ = dequeValContexts (fromCBVCtx Σ) (fromCBVCtx Γ)

    {-
    lemma₀ : ∀ τΣ Σ′ Γ → revContext (τΣ • Σ′) ⋎ Γ ≡ revContext Σ′ ⋎ (τΣ • Γ)
    lemma₀ τΣ Σ′ Γ = {!!}

    lemma : ∀ {τΣ Σ′ Γ τ} →
      Comp (fromCBVCtx (revContext (τΣ • Σ′) ⋎ Γ)) (cbvToCompType τ) →
      Comp (fromCBVCtx (revContext Σ′ ⋎ (τΣ • Γ))) (cbvToCompType τ)
    lemma {τΣ} {Σ′} {Γ} {τ} c = subst (λ x → Comp (fromCBVCtx x) (cbvToCompType τ)) (lemma₀ τΣ Σ′ Γ) c

    fromCBVConstCPSDo : ∀ {Γ Σ τ} → Terms Γ Σ → (Vals (fromCBVCtx Γ) (fromCBVCtx Σ) → Comp (fromCBVCtx (dequeContexts Σ Γ)) (cbvToCompType τ)) → Comp (fromCBVCtx Γ) (cbvToCompType τ)

    fromCBVConstCPSDo ∅ f = f ∅
    --fromCBVConstCPSDo (px • ∅) f = (fromCBV px) into f (vVar vThis • ∅)
    fromCBVConstCPSDo {Γ} {τΣ • Σ′} {τ} (px • ts) f = (fromCBV px) into {!!} -- (fromCBVConstCPSDo {τΣ • Γ} {Σ′} {τ} (map (weaken (drop_•_ τΣ ≼-refl)) ts) (λ vals → lemma {τΣ} {Σ′} {! f (vVar ? • {! weaken-vals (drop_••_ (cbvToValType τΣ) ≼≼-refl)!} vals!} )))
    -}
    fromCBVArg : ∀ {σ Γ τ} → Term Γ τ → (Val (cbvToValType τ • fromCBVCtx Γ) (cbvToValType τ) → Comp (cbvToValType τ • fromCBVCtx Γ) (cbvToCompType σ)) → Comp (fromCBVCtx Γ) (cbvToCompType σ)
    fromCBVArg t k = (fromCBV t) into k (vVar vThis)

    fromCBVArgs : ∀ {Σ Γ τ} → Terms Γ Σ → (Vals (dequeContexts Σ Γ) (fromCBVCtx Σ) → Comp (dequeContexts Σ Γ) (cbvToCompType τ)) → Comp (fromCBVCtx Γ) (cbvToCompType τ)
    fromCBVArgs ∅ k = k ∅
    fromCBVArgs {σ • Σ} {Γ} (t • ts) k = fromCBVArg t (λ v → fromCBVArgs (weaken-terms (drop_•_ _ ≼-refl) ts) (λ vs → k (weaken-val (dequeValContexts≼≼ (fromCBVCtx Σ) _) v • vs)))
    fromCBVConstCPSRoot : ∀ {Σ Γ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
    -- pass that as a closure to compose with (_•_ x) for each new variable.
    fromCBVConstCPSRoot c ts = fromCBVArgs ts (λ vs → cConst (cbvToCompConst c) vs) -- fromCBVConstCPSDo ts {!cConst (cbvToCompConst c)!}

-- In the beginning, we should get a function that expects a whole set of
-- arguments (Vals Γ Σ) for c, in the initial context Γ.
-- Later, each call should match:

-- -  Σ = τΣ • Σ′, then we recurse with Γ′ = τΣ • Γ and Σ′. Terms ought to be
--    weakened. The result of f (or the arguments) also ought to be weakened! So f should weaken
--    all arguments.

-- - Σ = ∅.

{-
  fromCBVConst : ∀ {Γ Σ τ} → Const Σ τ → Terms Γ Σ → Comp (fromCBVCtx Γ) (cbvToCompType τ)
  fromCBVConst c ts = cConstV2 c (cbvTermsToComps ts)
-}

  fromCBV (const c args) = fromCBVConstCPSRoot c args -- cConst (cbvToCompConst c) {!cbvTermsToComps args!} -- cConstVB2 c (cbvTermsToComps args)
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
