------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- The syntax of terms (Fig. 1a and 1b).
------------------------------------------------------------------------

-- The syntax of terms depends on the syntax of simple types
-- (because terms are indexed by types in order to rule out
-- ill-typed terms). But we are in the Parametric.* hierarchy, so
-- we don't know the full syntax of types, only how to lift the
-- syntax of base types into the syntax of simple types. This
-- means that we have to be parametric in the syntax of base
-- types, too.
--
-- In such parametric modules that depend on other parametric
-- modules, we first import our dependencies under a more
-- convenient name.

import Parametric.Syntax.Type as Type

-- Then we start the module proper, with parameters for all
-- extension points of our dependencies. Note that here, the
-- "Structure" naming convenion makes some sense, because we can
-- say that we need some "Type.Structure" in order to define the
-- "Term.Structure".

module Parametric.Syntax.Term
    (Base : Type.Structure)
  where

-- Now inside the module, we can open our dependencies with the
-- parameters for their extension points. Again, here the name
-- "Structure" makes some sense, because we can say that we want
-- to access the "Type.Structure" that is induced by Base.

open Type.Structure Base

-- At this point, we have dealt with the extension points of our
-- dependencies, and we have all the definitions about simple
-- types, contexts, variables, and variable sets in scope that we
-- provided in Parametric.Syntax.Type. Now we can proceed to
-- define our own extension point, following the pattern
-- explained in Parametric.Syntax.Type.

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function using (_∘_)
open import Data.Unit
open import Data.Sum

-- Our extension point is a set of primitives, indexed by the
-- types of their arguments and their return type. In general, if
-- you're confused about what an extension point means, you might
-- want to open the corresponding module in the Nehemiah
-- hierarchy to see how it is implemented in the example
-- plugin. In this case, that would be the Nehemiah.Syntax.Term
-- module.

Structure : Set₁
Structure = Context → Type → Set

module Structure (Const : Structure) where
  import Base.Data.DependentList as DependentList
  open DependentList public using (∅ ; _•_)
  open DependentList

  -- Declarations of Term and Terms to enable mutual recursion.
  --
  -- Note that terms are indexed by contexts and types. In the
  -- paper, we define the abstract syntax of terms in Fig 1a and
  -- then define a type system in Fig 1b. All lemmas and theorems
  -- then explicitly specify that they only hold for well-typed
  -- terms. Here, we use the indices to define a type that can
  -- only hold well-typed terms in the first place.
  data Term
    (Γ : Context) :
    (τ : Type) → Set

  -- (Terms Γ Σ) represents a list of terms with types from Σ
  -- with free variables bound in Γ.
  Terms : Context → Context → Set
  Terms Γ = DependentList (Term Γ)

  -- (Term Γ τ) represents a term of type τ
  -- with free variables bound in Γ.
  data Term Γ where
    -- constants aka. primitives can only occur fully applied.
    const : ∀ {Σ τ} →
      (c : Const Σ τ) →
      (args : Terms Γ Σ) →
      Term Γ τ
    var : ∀ {τ} →
      (x : Var Γ τ) →
      Term Γ τ
    app : ∀ {σ τ}
      (s : Term Γ (σ ⇒ τ)) →
      (t : Term Γ σ) →
      Term Γ τ
    -- we use de Bruijn indicies, so we don't need binding occurrences.
    abs : ∀ {σ τ}
      (t : Term (σ • Γ) τ) →
      Term Γ (σ ⇒ τ)

  -- Free variables
  FV : ∀ {τ Γ} → Term Γ τ → Vars Γ
  FV-terms : ∀ {Σ Γ} → Terms Γ Σ → Vars Γ

  FV (const ι ts) = FV-terms ts
  FV (var x) = singleton x
  FV (abs t) = tail (FV t)
  FV (app s t) = FV s ∪ FV t

  FV-terms ∅ = none
  FV-terms (t • ts) = FV t ∪ FV-terms ts

  closed? : ∀ {τ Γ} → (t : Term Γ τ) → (FV t ≡ none) ⊎ ⊤
  closed? t = empty? (FV t)

  -- Weakening

  weaken : ∀ {Γ₁ Γ₂ τ} →
    (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
    Term Γ₁ τ →
    Term Γ₂ τ

  weaken-terms : ∀ {Γ₁ Γ₂ Σ} →
    (Γ₁≼Γ₂ : Γ₁ ≼ Γ₂) →
    Terms Γ₁ Σ →
    Terms Γ₂ Σ

  weaken Γ₁≼Γ₂ (const c ts) = const c (weaken-terms Γ₁≼Γ₂ ts)
  weaken Γ₁≼Γ₂ (var x) = var (weaken-var Γ₁≼Γ₂ x)
  weaken Γ₁≼Γ₂ (app s t) = app (weaken Γ₁≼Γ₂ s) (weaken Γ₁≼Γ₂ t)
  weaken Γ₁≼Γ₂ (abs {σ} t) = abs (weaken (keep σ • Γ₁≼Γ₂) t)

  weaken-terms Γ₁≼Γ₂ ∅ = ∅
  weaken-terms Γ₁≼Γ₂ (t • ts) = weaken Γ₁≼Γ₂ t • weaken-terms Γ₁≼Γ₂ ts

  -- Specialized weakening
  weaken₁ : ∀ {Γ σ τ} →
    Term Γ τ → Term (σ • Γ) τ
  weaken₁ t = weaken (drop _ • ≼-refl) t

  weaken₂ : ∀ {Γ α β τ} →
    Term Γ τ → Term (α • β • Γ) τ
  weaken₂ t = weaken (drop _ • drop _ • ≼-refl) t

  weaken₃ : ∀ {Γ α β γ τ} →
    Term Γ τ → Term (α • β • γ • Γ) τ
  weaken₃ t = weaken (drop _ • drop _ • drop _ • ≼-refl) t

  -- Shorthands for nested applications
  app₂ : ∀ {Γ α β γ} →
    Term Γ (α ⇒ β ⇒ γ) →
    Term Γ α → Term Γ β → Term Γ γ
  app₂ f x = app (app f x)

  app₃ : ∀ {Γ α β γ δ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ
  app₃ f x = app₂ (app f x)

  app₄ : ∀ {Γ α β γ δ ε} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε
  app₄ f x = app₃ (app f x)

  app₅ : ∀ {Γ α β γ δ ε ζ} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ
  app₅ f x = app₄ (app f x)

  app₆ : ∀ {Γ α β γ δ ε ζ η} →
    Term Γ (α ⇒ β ⇒ γ ⇒ δ ⇒ ε ⇒ ζ ⇒ η) →
    Term Γ α → Term Γ β → Term Γ γ → Term Γ δ →
    Term Γ ε → Term Γ ζ → Term Γ η
  app₆ f x = app₅ (app f x)

  UncurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
  UncurriedTermConstructor Γ Σ τ = Terms Γ Σ → Term Γ τ

  uncurriedConst : ∀ {Σ τ} → Const Σ τ → ∀ {Γ} → UncurriedTermConstructor Γ Σ τ
  uncurriedConst constant = const constant

  CurriedTermConstructor : (Γ Σ : Context) (τ : Type) → Set
  CurriedTermConstructor Γ ∅ τ′ = Term Γ τ′
  CurriedTermConstructor Γ (τ • Σ) τ′ = Term Γ τ → CurriedTermConstructor Γ Σ τ′

  curryTermConstructor : ∀ {Σ Γ τ} → UncurriedTermConstructor Γ Σ τ → CurriedTermConstructor Γ Σ τ
  curryTermConstructor {∅} k = k ∅
  curryTermConstructor {τ • Σ} k = λ t → curryTermConstructor (λ ts → k (t • ts))

  curriedConst : ∀ {Σ τ} → Const Σ τ → ∀ {Γ} → CurriedTermConstructor Γ Σ τ
  curriedConst constant = curryTermConstructor (uncurriedConst constant)


  -- HOAS-like smart constructors for lambdas, for different arities.

  -- We could also write this:
  module NamespaceForBadAbs₁ where
    abs₁′ :
      ∀ {Γ τ₁ τ} →
        (Term (τ₁ • Γ) τ₁ → Term (τ₁ • Γ) τ) →
        (Term Γ (τ₁ ⇒ τ))
    abs₁′ {Γ} {τ₁} = λ f → abs (f (var this))

  -- However, this is less general, and it is harder to reuse. In particular,
  -- this cannot be used inside abs₂, ..., abs₆.

  -- Now, let's write other variants with a loop!
  open import Data.Vec using (_∷_; []; Vec; foldr; [_]; reverse)
  open import Data.Nat
  module AbsNHelpers where
    open import Function
    hoasArgType : ∀ {n} → Context → Type → Vec Type n → Set
    hoasArgType Γ τres = foldr _ (λ a b → a → b) (Term Γ τres) ∘ Data.Vec.map (Term Γ)
    -- That is,
    --hoasArgType Γ τres [] = Term Γ τres
    --hoasArgType Γ τres (τ₀ ∷ τs) = Term Γ τ₀ → hoasArgType Γ τres τs

    hoasResType : ∀ {n} → Type → Vec Type n → Type
    hoasResType τres = foldr _ _⇒_ τres

    absNType : {n : ℕ} → Vec _ n → Set
    absNType τs = ∀ {Γ τres} →
      (f : ∀ {Γ′} → {Γ≼Γ′ : Γ ≼ Γ′} → hoasArgType Γ′ τres τs) →
      Term Γ (hoasResType τres τs)

    drop-≼-l : ∀ {Γ Γ′ τ} → (τ • Γ ≼ Γ′) → Γ ≼ Γ′
    drop-≼-l Γ′≼Γ′₁ = ≼-trans (drop _ • ≼-refl) Γ′≼Γ′₁

    absN : {n : ℕ} → (τs : Vec _ n) → absNType τs
    absN []        f = f {Γ≼Γ′ = ≼-refl}
    absN (τ₁ ∷ τs) f =
      abs (absN τs
        (λ {_} {Γ′≼Γ′₁} →
          f
            {Γ≼Γ′ = drop-≼-l Γ′≼Γ′₁}
            (weaken Γ′≼Γ′₁ (var this))))

    -- Using a similar trick, we can declare absV (where V stands for variadic),
    -- which takes the N implicit type arguments individually, collects them and
    -- passes them on to absN. This is inspired by the example in the Agda 2.4.0
    -- release notes about support for varying arity. To collect them, we need
    -- to use an accumulator argument.

    absVType : ∀ n {m} (τs : Vec Type m) → Set
    absVType zero       τs = absNType (reverse τs)
    absVType (suc n) τs = {τ₁ : Type} → absVType n (τ₁ ∷ τs)

    absVAux : ∀ {m} → (τs : Vec Type m) → ∀ n → absVType n τs
    absVAux τs zero    = absN (reverse τs)
    -- (Support for varying arity does not work here, so {τ₁} must be bound in
    -- the right-hand side).
    absVAux τs (suc n) = λ {τ₁} → absVAux (τ₁ ∷ τs) n

    -- "Initialize" accumulator to the empty list.
    absV = absVAux []
    -- We could maybe define absV directly, without going through absN, by
    -- making hoasArgType and hoasResType also variadic, but I don't see a clear
    -- advantage.

  open AbsNHelpers using (absV) public

  {-
  Example types:
  absV 1:
    {τ₁ : Type} {Γ : Context} {τres : Type} →
      ({Γ′ : Context} {Γ≼Γ′ : Γ ≼ Γ′} → Term Γ′ τ₁ → Term Γ′ τres) →
      Term Γ (τ₁ ⇒ τres)

  absV 2:
    {τ₁ : Type} {τ₁ = τ₂ : Type} {Γ : Context} {τres : Type} →
      ({Γ′ : Context} {Γ≼Γ′ : Γ ≼ Γ′} →
       Term Γ′ τ₁ → Term Γ′ τ₂ → Term Γ′ τres) →
      Term Γ (τ₁ ⇒ τ₂ ⇒ τres)

  -}
  -- (Terms Γ Σ) represents a list of terms with types from Σ
  -- with free variables bound in Γ.
  mutual
    Vals : ValContext → ValContext → Set
    Vals Γ = DependentList (Val Γ)

    Comps : ValContext → List CompType → Set
    Comps Γ = DependentList (Comp Γ)

    data Val Γ : (τ : ValType) → Set where
      vVar : ∀ {τ} (x : ValVar Γ τ) → Val Γ τ
      vThunk : ∀ {τ} → Comp Γ τ → Val Γ (U τ)

    data Comp Γ : (τ : CompType) → Set where
      -- Treating all constants as computations is a hack (think of constant values) but they can always be thunked.
      -- Using cbnToCompType is an even bigger hack.
      cConst : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Vals Γ (fromCBNCtx Σ)) →
        Comp Γ (cbnToCompType τ)
      -- So let's try adding another kind of constant for CBV.
      cConstV : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Vals Γ (fromCBVCtx Σ)) →
        Comp Γ (cbvToCompType τ)
      -- In fact, converting to cConstV c is rather hard.
      -- Let's make the job simpler for now.
      cConstV2 : ∀ {Σ τ} →
        (c : Const Σ τ) →
        (args : Comps Γ (fromCBVToCompList Σ)) →
        Comp Γ (cbvToCompType τ)
      -- This should be transformed to
      --
      --   arg1 to x1 in (arg2 to x2 in ... (argn to xn in (cConstV c (x1 :: x2 :: ... xn)))).
      --
      -- But it's not trivial to write the recursive functions needed for that. So let's punt for now.

      cForce : ∀ {τ} → Val Γ (U τ) → Comp Γ τ
      cProduce : ∀ {τ} (v : Val Γ τ) → Comp Γ (F τ)
      -- Originally, M to x in N. But here we have no names!
      _into_ : ∀ {σ τ} →
        (e₁ : Comp Γ (F σ)) →
        (e₂ : Comp (σ •• Γ) τ) →
        Comp Γ τ
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

  fromCBN (const c args) = cConst c (fromCBNTerms args)
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

  fromCBV (const c args) = cConstV2 c (cbvTermsToComps args)
    --fromCBVConst c args
  fromCBV (app s t) =
    (fromCBV s) into
      ((fromCBV (weaken (drop _ • ≼-refl) t)) into
        cApp (cForce (vVar (vThat vThis))) (vVar vThis))
  -- Values
  fromCBV (var x) = cProduce (vVar (fromVar cbvToValType x))
  fromCBV (abs t) = cProduce (vThunk (cAbs (fromCBV t)))

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
