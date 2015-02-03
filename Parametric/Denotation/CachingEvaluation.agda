------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Caching evaluation
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term

import Parametric.Syntax.MType as MType
import Parametric.Syntax.MTerm as MTerm

import Parametric.Denotation.Value as Value
import Parametric.Denotation.Evaluation as Evaluation
import Parametric.Denotation.MValue as MValue
import Parametric.Denotation.CachingMValue as CachingMValue
import Parametric.Denotation.MEvaluation as MEvaluation

module Parametric.Denotation.CachingEvaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
    (⟦_⟧Const : Evaluation.Structure Const ⟦_⟧Base)
    (ValConst : MTerm.ValConstStructure Const)
    (CompConst : MTerm.CompConstStructure Const)
    -- I should really switch to records - can it get sillier than this?
    (⟦_⟧ValBase : MEvaluation.ValStructure Const ⟦_⟧Base ValConst CompConst)
    (⟦_⟧CompBase : MEvaluation.CompStructure Const ⟦_⟧Base ValConst CompConst)
  where

open Type.Structure Base
open Term.Structure Base Const

open MType.Structure Base
open MTerm.Structure Const ValConst CompConst

open Value.Structure Base ⟦_⟧Base
open Evaluation.Structure Const ⟦_⟧Base ⟦_⟧Const
open MValue.Structure Base ⟦_⟧Base
open CachingMValue.Structure Base ⟦_⟧Base
open MEvaluation.Structure Const ⟦_⟧Base ValConst CompConst ⟦_⟧ValBase ⟦_⟧CompBase

open import Base.Denotation.Notation

-- Extension Point: Evaluation of fully applied constants.
ValStructure : Set
ValStructure = ∀ {Σ τ} → ValConst Σ τ → ⟦ Σ ⟧ValCtxHidCache → ⟦ τ ⟧ValTypeHidCache

CompStructure : Set
CompStructure = ∀ {Σ τ} → CompConst Σ τ → ⟦ Σ ⟧ValCtxHidCache → ⟦ τ ⟧CompTypeHidCache

module Structure
       (⟦_⟧ValBaseTermCache  : ValStructure)
       (⟦_⟧CompBaseTermCache : CompStructure)
    where

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
  open import Data.Unit

  -- Defining a caching semantics for Term proves to be hard, requiring to
  -- insert and remove caches where we apply constants.

  -- Indeed, our plugin interface is not satisfactory for adding caching. CBPV can help us.

  -- The solution is to distinguish among different kinds of constants. Some are
  -- value constructors (and thus do not return caches), while others are
  -- computation constructors (and thus should return caches). For products, I
  -- believe we will only use the products which are values, not computations
  -- (XXX check CBPV paper for the name).
  ⟦_⟧CompTermCache : ∀ {τ Γ} → Comp Γ τ → ⟦ Γ ⟧ValCtxHidCache → ⟦ τ ⟧CompTypeHidCache
  ⟦_⟧ValTermCache : ∀ {τ Γ} → Val Γ τ → ⟦ Γ ⟧ValCtxHidCache → ⟦ τ ⟧ValTypeHidCache
  ⟦_⟧ValsTermCache : ∀ {Γ Σ} → Vals Γ Σ → ⟦ Γ ⟧ValCtxHidCache → ⟦ Σ ⟧ValCtxHidCache

  open import Base.Denotation.Environment ValType ⟦_⟧ValTypeHidCache public
    using ()
    renaming (⟦_⟧Var to ⟦_⟧ValVarHidCache)

  -- This says that the environment does not contain caches... sounds wrong!
  -- Either we add extra variables for the caches, or we store computations in
  -- the environment (but that does not make sense), or we store caches in
  -- values, by acting not on F but on something else (U?).

  -- Copy of ⟦_⟧Vals
  ⟦ ∅ ⟧ValsTermCache ρ = ∅
  ⟦ vt • valtms ⟧ValsTermCache ρ = ⟦ vt ⟧ValTermCache ρ • ⟦ valtms ⟧ValsTermCache ρ

  -- I suspect the plan was to use extra variables; that's annoying to model in
  -- Agda but easier in implementations.

  ⟦ vVar   x ⟧ValTermCache ρ = ⟦ x ⟧ValVarHidCache ρ
  ⟦ vThunk x ⟧ValTermCache ρ = ⟦ x ⟧CompTermCache ρ
  -- No caching, because the arguments are values, so evaluating them does not
  -- produce intermediate results.
  ⟦ vConst c args ⟧ValTermCache ρ = ⟦ c ⟧ValBaseTermCache (⟦ args ⟧ValsTermCache ρ)

  -- The only caching is done by the interpretation of the constant (because the
  -- arguments are values so need no caching).
  ⟦_⟧CompTermCache (cConst c args) ρ = ⟦ c ⟧CompBaseTermCache (⟦ args ⟧ValsTermCache ρ)

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

  -- Here, unlike in ⟦_⟧TermCache, we don't need to invent an empty cache,
  -- that's moved into the handling of cReturn. This makes *the* difference for
  -- nested lambdas, where we don't need to create caches multiple times!

  ⟦_⟧CompTermCache (cAbs v) ρ = λ x → ⟦ v ⟧CompTermCache (x • ρ)

  -- Here we see that we are in a sort of A-normal form, because the argument is
  -- a value (not quite ANF though, since values can be thunks - that is,
  -- computations which haven't been run yet, I guess. Do we have an use for
  -- that? That allows passing lambdas as arguments directly - which is fine,
  -- because producing a closure indeed does not have intermediate results!).
  ⟦_⟧CompTermCache (cApp t v) ρ = ⟦ t ⟧CompTermCache ρ (⟦ v ⟧ValTermCache ρ)
