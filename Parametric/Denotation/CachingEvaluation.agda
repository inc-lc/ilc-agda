------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Caching evaluation
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation

module Parametric.Denotation.CachingEvaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const

open import Base.Denotation.Notation

open import Relation.Binary.PropositionalEquality

module Structure where
  {-
  -- Prototype here the type-correctness of a simple non-standard semantics.
  -- This describes a simplified version of the transformation by Liu and
  -- Tanenbaum, PEPM 1995 - but for now, instead of producing object language
  -- terms, we produce host language terms to take advantage of the richer type
  -- system of the host language (in particular, here we need the unit type,
  -- product types and *existentials*).
  --
  -- As usual, we'll later switch to a real term transformation.
  -}
  open import Data.Product hiding (map)
  open import Data.Sum hiding (map)
  open import Data.Unit
  open import Level

  -- Type semantics for this scenario.
  ⟦_⟧TypeHidCache : (τ : Type) → Set₁
  ⟦ base ι ⟧TypeHidCache = Lift ⟦ base ι ⟧
  ⟦ σ ⇒ τ ⟧TypeHidCache = ⟦ σ ⟧TypeHidCache → (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧TypeHidCache × τ₁ )

  open import Parametric.Syntax.MType as MType
  open MType.Structure Base
  open import Parametric.Syntax.MTerm as MTerm
  open MTerm.Structure Const

  open import Function hiding (const)

  ⟦_⟧ValType : (τ : ValType) → Set
  ⟦_⟧CompType : (τ : CompType) → Set

  ⟦ U c ⟧ValType = ⟦ c ⟧CompType
  ⟦ B ι ⟧ValType = ⟦ base ι ⟧
  ⟦ vUnit ⟧ValType = ⊤
  ⟦ τ₁ v× τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType × ⟦ τ₂ ⟧ValType
  ⟦ τ₁ v+ τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType ⊎ ⟦ τ₂ ⟧ValType

  ⟦ F τ ⟧CompType = ⟦ τ ⟧ValType
  ⟦ σ ⇛ τ ⟧CompType = ⟦ σ ⟧ValType → ⟦ τ ⟧CompType

  -- XXX: below we need to override just a few cases. Inheritance would handle
  -- this precisely; without inheritance, we might want to use one of the
  -- standard encodings of related features (delegation?).

  ⟦_⟧ValTypeHidCacheWrong : (τ : ValType) → Set₁
  ⟦_⟧CompTypeHidCacheWrong : (τ : CompType) → Set₁

  -- This line is the only change, up to now, for the caching semantics starting from CBPV.
  ⟦ F τ ⟧CompTypeHidCacheWrong = (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧ValTypeHidCacheWrong × τ₁ )
  -- Delegation upward.
  ⟦ τ ⟧CompTypeHidCacheWrong = Lift ⟦ τ ⟧CompType
  ⟦_⟧ValTypeHidCacheWrong = Lift ∘ ⟦_⟧ValType
  -- The above does not override what happens in recursive occurrences.

  {-# NO_TERMINATION_CHECK #-}
  ⟦_⟧ValTypeHidCache : (τ : ValType) → Set
  ⟦_⟧CompTypeHidCache : (τ : CompType) → Set

  ⟦ U c ⟧ValTypeHidCache = ⟦ c ⟧CompTypeHidCache
  ⟦ B ι ⟧ValTypeHidCache = ⟦ base ι ⟧
  ⟦ vUnit ⟧ValTypeHidCache = ⊤
  ⟦ τ₁ v× τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache × ⟦ τ₂ ⟧ValTypeHidCache
  ⟦ τ₁ v+ τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache ⊎ ⟦ τ₂ ⟧ValTypeHidCache

  -- This line is the only change, up to now, for the caching semantics.
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
  ⟦ F τ ⟧CompTypeHidCache = (Σ[ τ₁ ∈ ValType ] ⟦ τ ⟧ValTypeHidCache × ⟦ τ₁ ⟧ValTypeHidCache )
  ⟦ σ ⇛ τ ⟧CompTypeHidCache = ⟦ σ ⟧ValTypeHidCache → ⟦ τ ⟧CompTypeHidCache

  ⟦_⟧CtxHidCache : (Γ : Context) → Set₁
  ⟦_⟧CtxHidCache = DependentList ⟦_⟧TypeHidCache

  ⟦_⟧ValCtxHidCache : (Γ : ValContext) → Set
  ⟦_⟧ValCtxHidCache = DependentList ⟦_⟧ValTypeHidCache

  {-
  ⟦_⟧CompCtxHidCache : (Γ : CompContext) → Set₁
  ⟦_⟧CompCtxHidCache = DependentList ⟦_⟧CompTypeHidCache
  -}

  -- It's questionable that this is not polymorphic enough.
  ⟦_⟧VarHidCache : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧CtxHidCache → ⟦ τ ⟧TypeHidCache
  ⟦ this ⟧VarHidCache (v • ρ) = v
  ⟦ that x ⟧VarHidCache (v • ρ) = ⟦ x ⟧VarHidCache ρ

  -- Now, let us define a caching semantics for terms.

  -- This proves to be hard, because we need to insert and remove caches where
  -- we apply constants.

  -- Indeed, our plugin interface is not satisfactory for adding caching. CBPV can help us.

  --
  -- Inserting and removing caches --
  --

  -- Implementation note: The mutual recursion looks like a fold on exponentials, where you need to define the function and the inverse at the same time.
  -- Indeed, both functions seem structurally recursive on τ.
  dropCache : ∀ {τ} → ⟦ τ ⟧TypeHidCache → ⟦ τ ⟧
  extend : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧TypeHidCache

  dropCache {base ι} v = lower v
  dropCache {σ ⇒ τ} v x = dropCache (proj₁ (proj₂ (v (extend x))))

  extend {base ι} v = lift v
  extend {σ ⇒ τ} v = λ x → , (extend (v (dropCache x)) , tt)

  -- OK, this version is syntax-directed, luckily enough, except on primitives
  -- (as expected). This reveals a bug of ours on higher-order primitives.
  --
  -- Moreover, we can somewhat safely assume that each call to extend and to
  -- dropCache is bad: then we see that the handling of constants is bad. That's
  -- correct, because constants will not return intermediate results in this
  -- schema :-(.
  ⟦_⟧TermCache2 : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧CtxHidCache → ⟦ τ ⟧TypeHidCache
  ⟦_⟧TermCache2 (const c args) ρ = extend (⟦ const c args ⟧ (map dropCache ρ))
  ⟦_⟧TermCache2 (var x) ρ = ⟦ x ⟧VarHidCache ρ

  -- It seems odd (a probable bug?) that the result of t needn't be stripped of
  -- its cache.
  ⟦_⟧TermCache2 (app s t) ρ = proj₁ (proj₂ ((⟦ s ⟧TermCache2 ρ) (⟦ t ⟧TermCache2 ρ)))

  -- Provide an empty cache!
  ⟦_⟧TermCache2 (abs t) ρ x = , (⟦ t ⟧TermCache2 (x • ρ) , tt)

  -- The solution is to distinguish among different kinds of constants. Some are
  -- value constructors (and thus do not return caches), while others are
  -- computation constructors (and thus should return caches). For products, I
  -- believe we will only use the products which are values, not computations
  -- (XXX check CBPV paper for the name).
  ⟦_⟧CompTermCache : ∀ {τ Γ} → Comp Γ τ → ⟦ Γ ⟧ValCtxHidCache → ⟦ τ ⟧CompTypeHidCache
  ⟦_⟧ValTermCache : ∀ {τ Γ} → Val Γ τ → ⟦ Γ ⟧ValCtxHidCache → ⟦ τ ⟧ValTypeHidCache

  open import Base.Denotation.Environment ValType ⟦_⟧ValTypeHidCache public
    using ()
    renaming (⟦_⟧Var to ⟦_⟧ValVar)

  -- This says that the environment does not contain caches... sounds wrong!
  -- Either we add extra variables for the caches, or we store computations in
  -- the environment (but that does not make sense), or we store caches in
  -- values, by acting not on F but on something else (U?).

  -- I suspect the plan was to use extra variables; that's annoying to model in
  -- Agda but easier in implementations.

  ⟦ vVar   x ⟧ValTermCache ρ = ⟦ x ⟧ValVar ρ
  ⟦ vThunk x ⟧ValTermCache ρ = ⟦ x ⟧CompTermCache ρ

  -- The real deal, finally.
  open import UNDEFINED
  -- XXX constants are still a slight mess because I'm abusing CBPV...
  -- (Actually, I just forgot the difference, and believe I had too little clue
  -- when I wrote these constructors... but some of them did make sense).
  ⟦_⟧CompTermCache (cConst c args) ρ = reveal UNDEFINED
  ⟦_⟧CompTermCache (cConstV c args) ρ = reveal UNDEFINED
  ⟦_⟧CompTermCache (cConstV2 c args) ρ = reveal UNDEFINED

  -- Also, where are introduction forms for pairs and sums among values? With
  -- them, we should see that we can interpret them without adding a cache.

  -- Thunks keep seeming noops.
  ⟦_⟧CompTermCache (cForce x) ρ = ⟦ x ⟧ValTermCache ρ

  -- Here, in an actual implementation, we would return the actual cache with
  -- all variables.
  --
  -- The effect of F is a writer monad of cached values, where the monoid is
  -- (isomorphic to) the free monoid over (∃ τ . τ), but we push the
  -- existentials up when pairing things!

  -- That's what we're interpreting computations in. XXX maybe consider using
  -- monads directly. But that doesn't deal with arity.
  ⟦_⟧CompTermCache (cReturn v) ρ = vUnit , (⟦ v ⟧ValTermCache ρ , tt)

  -- For this to be enough, a lambda needs to return a produce, not to forward
  -- the underlying one (unless there are no intermediate results). The correct
  -- requirements can maybe be enforced through a linear typing discipline.

  {-
  -- Here we'd have a problem with the original into from CBPV, because it does
  -- not require converting expressions to the "CBPV A-normal form".

  ⟦_⟧CompTermCache (v₁ into v₂) ρ =
  -- Sequence commands and combine their caches.
  {-
    let (_ , (r₁ , c₁)) = ⟦ v₁ ⟧CompTermCache ρ
        (_ , (r₂ , c₂)) = ⟦ v₂ ⟧CompTermCache (r₁ • ρ)
    in , (r₂ , (c₁ ,′ c₂))
  -}

  -- The code above does not work, because we only guarantee that v₂ is
  -- a computation, not that it's an F-computation - v₂ could also be function
  -- type or a computation product.

  -- We need a restricted CBPV, where these two possibilities are forbidden. If
  -- you want to save something between different lambdas, you need to add an F
  -- U to reflect that. (Double-check the papers which show how to encode arity
  -- using CBPV, it seems that they should find the same problem --- XXX they
  -- don't).

  -- Instead, just drop the first cache (XXX WRONG).
    ⟦ v₂ ⟧CompTermCache (proj₁ (proj₂ (⟦ v₁ ⟧CompTermCache ρ)) • ρ)
  -}

  -- But if we alter _into_ as described above, composing the caches works!
  -- However, we should not forget we also need to save the new intermediate
  -- result, that is the one produced by the first part of the let.
  ⟦_⟧CompTermCache (_into_ {σ} {τ} v₁ v₂) ρ =
    let (τ₁ , (r₁ , c₁)) = ⟦ v₁ ⟧CompTermCache ρ
        (τ₂ , (r₂ , c₂)) = ⟦ v₂ ⟧CompTermCache (r₁ • ρ)
    in  (σ v× τ₁ v× τ₂) , (r₂ ,′ ( r₁  ,′ c₁ ,′ c₂))

  -- Note the compositionality and luck: we don't need to do anything at the
  -- cReturn time, we just need the nested into to do their job, because as I
  -- said intermediate results are a writer monad.
  --
  -- Q: But then, do we still need to do all the other stuff? IOW, do we still
  -- need to forbid (λ x . y <- f args; g args') and replace it with (λ x . y <-
  -- f args; z <- g args'; z)?
  --
  -- A: One thing we still need is using the monadic version of into for the
  -- same reasons - which makes sense, since it has the type of monadic bind.
  --
  -- Maybe not: if we use a monad, which respects left and right identity, the
  -- two above forms are equivalent. But what about associativity? We don't have
  -- associativity with nested tuples in the middle. That's why the monad uses
  -- lists! We can also use nested tuple, as long as in the into case we don't
  -- do (a, b) but append a b (ahem, where?), which decomposes the first list
  -- and prepends it to the second. To this end, we need to know the type of the
  -- first element, or to ensure it's always a pair. Maybe we just want to reuse
  -- an HList.

  -- In abstractions, we should start collecting all variables...

  -- Here, unlike in ⟦_⟧TermCache2, we don't need to invent an empty cache,
  -- that's moved into the handling of cReturn. This makes *the* difference for
  -- nested lambdas, where we don't need to create caches multiple times!

  ⟦_⟧CompTermCache (cAbs v) ρ x = ⟦ v ⟧CompTermCache (x • ρ)

  -- Here we see that we are in a sort of A-normal form, because the argument is
  -- a value (not quite ANF though, since values can be thunks - that is,
  -- computations which haven't been run yet, I guess. Do we have an use for
  -- that? That allows passing lambdas as arguments directly - which is fine,
  -- because producing a closure indeed does not have intermediate results!).
  ⟦_⟧CompTermCache (cApp t v) ρ = ⟦ t ⟧CompTermCache ρ (⟦ v ⟧ValTermCache ρ)
