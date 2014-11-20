------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Standard evaluation (Def. 3.3 and Fig. 4i)
------------------------------------------------------------------------

import Parametric.Syntax.Type as Type
import Parametric.Syntax.Term as Term
import Parametric.Denotation.Value as Value

module Parametric.Denotation.Evaluation
    {Base : Type.Structure}
    (Const : Term.Structure Base)
    (⟦_⟧Base : Value.Structure Base)
  where

open Type.Structure Base
open Term.Structure Base Const
open Value.Structure Base ⟦_⟧Base

open import Base.Denotation.Notation

open import Relation.Binary.PropositionalEquality
open import Theorem.CongApp
open import Postulate.Extensionality

-- Extension Point: Evaluation of fully applied constants.
Structure : Set
Structure = ∀ {Σ τ} → Const Σ τ → ⟦ Σ ⟧ → ⟦ τ ⟧

module Structure (⟦_⟧Const : Structure) where
  ⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧

  ⟦_⟧Terms : ∀ {Γ Σ} → Terms Γ Σ → ⟦ Γ ⟧ → ⟦ Σ ⟧

  -- We provide: Evaluation of arbitrary terms.
  ⟦ const c args ⟧Term ρ = ⟦ c ⟧Const (⟦ args ⟧Terms ρ)
  ⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
  ⟦ app s t ⟧Term ρ = (⟦ s ⟧Term ρ) (⟦ t ⟧Term ρ)
  ⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)

  -- this is what we'd like to write.
  -- unfortunately termination checker complains.
  --
  --   ⟦ terms ⟧Terms ρ = map-IVT (λ t → ⟦ t ⟧Term ρ) terms
  --
  -- so we do explicit pattern matching instead.
  ⟦ ∅ ⟧Terms ρ = ∅
  ⟦ s • terms ⟧Terms ρ = ⟦ s ⟧Term ρ • ⟦ terms ⟧Terms ρ
  
  meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
  meaningOfTerm = meaning ⟦_⟧Term

  weaken-sound : ∀ {Γ₁ Γ₂ τ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
    (t : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ₁≼Γ₂ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ₁≼Γ₂ ⟧ ρ)

  weaken-terms-sound : ∀ {Γ₁ Γ₂ Σ} {Γ₁≼Γ₂ : Γ₁ ≼ Γ₂}
    (terms : Terms Γ₁ Σ) (ρ : ⟦ Γ₂ ⟧) →
    ⟦ weaken-terms Γ₁≼Γ₂ terms ⟧Terms ρ ≡ ⟦ terms ⟧Terms (⟦ Γ₁≼Γ₂ ⟧ ρ)

  weaken-terms-sound ∅ ρ = refl
  weaken-terms-sound (t • terms) ρ =
    cong₂ _•_ (weaken-sound t ρ) (weaken-terms-sound terms ρ)

  weaken-sound {Γ₁≼Γ₂ = Γ₁≼Γ₂} (var x) ρ = weaken-var-sound Γ₁≼Γ₂ x ρ
  weaken-sound (app s t) ρ = weaken-sound s ρ ⟨$⟩ weaken-sound t ρ
  weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
  weaken-sound {Γ₁} {Γ₂} {Γ₁≼Γ₂ = Γ₁≼Γ₂} (const {Σ} {τ} c args) ρ =
    cong ⟦ c ⟧Const (weaken-terms-sound args ρ)

  {-
  -- Prototype here the type-correctness of a simple non-standard semantics.
  -- This describes a simplified version of the transformation by Liu and
  -- Tanenbaum, PEPM 1995 - but instead of producing object language terms, we
  -- produce host language terms to take advantage of the richer type system of
  -- the host language (in particular, here we need the unit type, product types
  -- and *existentials*).
  -}
  open import Data.Product hiding (map)
  open import Data.Sum hiding (map)
  open import Data.Unit

  -- A semantics for empty caching semantics
  ⟦_⟧Type2 : (τ : Type) → Set
  ⟦ base ι ⟧Type2 = ⟦ base ι ⟧
  ⟦ σ ⇒ τ ⟧Type2 = ⟦ σ ⟧Type → (⟦ τ ⟧Type × ⊤)

  open import Level

  {-
  -- Hidden cache semantics, try 1.
  --
  -- Wrong: even the inputs should be extended.
  -- It's just that extension on base values does nothing interesting.

  ⟦_⟧TypeHidCache : (τ : Type) → Set₁
  ⟦ base ι ⟧TypeHidCache = Lift ⟦ base ι ⟧
  ⟦ σ ⇒ τ ⟧TypeHidCache =  ⟦ σ ⟧Type → (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧TypeHidCache × τ₁ )
  -- This type would be cooler, but it also places "excessive" requirements on
  -- the object language compared to what we formalize - e.g., unit types.
  --
  --⟦ σ ⇒ τ ⟧TypeHidCache = ⟦ σ ⟧Type → (Σ[ τ₁ ∈ Type ] ⟦ τ ⟧Type × ⟦ τ₁ ⟧Type )

  extend : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧TypeHidCache
  extend {base ι} v = lift v
  extend {σ ⇒ τ} v = λ x → ⊤ , (extend (v x) , tt)

  dropCache : ∀ {τ} → ⟦ τ ⟧TypeHidCache → ⟦ τ ⟧
  dropCache {base ι} v = lower v
  dropCache {σ ⇒ τ} v x = dropCache (proj₁ (proj₂ (v x)))

  -- Wrong type signature:
  ⟦_⟧TermCache : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧TypeHidCache
  ⟦_⟧TermCache (const c args) ρ = {!!}
  -- Oh. We don't even know what to return without matching on the type. That's
  -- also true in our term transformation: we need to eta-expand also
  -- non-primitives (higher-order arguments) for everything to possibly work.
  -- Hm... or we need to have extended values in the environment - where the extension is again just for functions.
  ⟦_⟧TermCache (var x) ρ = extend (⟦ var x ⟧ ρ)
  -- XXX: this delegates to standard evaluation, I'm not sure whether we should do that.
  -- In fact, we should use our evaluation and select from the result.
  ⟦_⟧TermCache (app s t) ρ = proj₁ (proj₂ ((⟦ s ⟧TermCache ρ) (⟦ t ⟧Term ρ)))
  -- Provide an empty cache :-)!
  ⟦_⟧TermCache (abs t) ρ x = ⊤ , (⟦ t ⟧TermCache (x • ρ) , tt)


  -- Wrong type definitions: functions get argument of transformed types.
  ⟦_⟧CtxHidCache : (Γ : Context) → Set₁
  ⟦_⟧CtxHidCache = DependentList ⟦_⟧TypeHidCache

  ⟦_⟧VarHidCache : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧CtxHidCache → ⟦ τ ⟧TypeHidCache
  ⟦ this ⟧VarHidCache (v • ρ) = v
  ⟦ that x ⟧VarHidCache (v • ρ) = ⟦ x ⟧VarHidCache ρ

  ⟦_⟧TermCache2 : ∀ {τ Γ} → Term Γ τ → ⟦ Γ ⟧CtxHidCache → ⟦ τ ⟧TypeHidCache
  ⟦_⟧TermCache2 (const c args) ρ = {!!}
  ⟦_⟧TermCache2 (var x) ρ = ⟦ x ⟧VarHidCache ρ
  ⟦_⟧TermCache2 (app s t) ρ = proj₁ (proj₂ ((⟦ s ⟧TermCache2 ρ) (dropCache (⟦ t ⟧TermCache2 ρ))))
  -- Provide an empty cache :-)!
  ⟦_⟧TermCache2 (abs t) ρ x = ⊤ , (⟦ t ⟧TermCache2 ((extend x) • ρ) , tt)
  -}

  -- Type semantics for this scenario.
  ⟦_⟧TypeHidCache : (τ : Type) → Set₁
  ⟦ base ι ⟧TypeHidCache = Lift ⟦ base ι ⟧
  ⟦ σ ⇒ τ ⟧TypeHidCache = ⟦ σ ⟧TypeHidCache → (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧TypeHidCache × τ₁ )

  open import Parametric.Syntax.CBPVType as CBPVType
  open CBPVType.Structure Base
  open import Parametric.Syntax.CBPVTerm as CBPVTerm
  open CBPVTerm.Structure Const

  open import Function hiding (const)

  ⟦_⟧ValType : (τ : ValType) → Set
  ⟦_⟧CompType : (τ : CompType) → Set

  ⟦ U c ⟧ValType = ⟦ c ⟧CompType
  ⟦ B ι ⟧ValType = ⟦ base ι ⟧
  ⟦ vUnit ⟧ValType = Lift Unit
  ⟦ τ₁ v× τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType × ⟦ τ₂ ⟧ValType
  ⟦ τ₁ v+ τ₂ ⟧ValType = ⟦ τ₁ ⟧ValType ⊎ ⟦ τ₂ ⟧ValType

  ⟦ F τ ⟧CompType = ⟦ τ ⟧ValType
  ⟦ σ ⇛ τ ⟧CompType = ⟦ σ ⟧ValType → ⟦ τ ⟧CompType
  ⟦ τ₁ Π τ₂ ⟧CompType = ⟦ τ₁ ⟧CompType × ⟦ τ₂ ⟧CompType

  -- XXX: below we need to override just a few cases. Inheritance would handle
  -- this precisely; without inheritance, we might want to use one of the
  -- standard encodings of related features (delegation?).

  ⟦_⟧ValTypeHidCacheWrong : (τ : ValType) → Set₁
  ⟦_⟧CompTypeHidCacheWrong : (τ : CompType) → Set₁

  -- This line is the only change, up to now, for the caching semantics starting from CBPV.>
  ⟦ F τ ⟧CompTypeHidCacheWrong = (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧ValTypeHidCacheWrong × τ₁ )
  -- Delegation upward.
  ⟦ τ ⟧CompTypeHidCacheWrong = Lift ⟦ τ ⟧CompType
  ⟦_⟧ValTypeHidCacheWrong = Lift ∘ ⟦_⟧ValType
  -- The above does not override what happens in recursive occurrences.

  ⟦_⟧ValTypeHidCache : (τ : ValType) → Set₁
  ⟦_⟧CompTypeHidCache : (τ : CompType) → Set₁

  ⟦ U c ⟧ValTypeHidCache = ⟦ c ⟧CompTypeHidCache
  ⟦ B ι ⟧ValTypeHidCache = Lift ⟦ base ι ⟧
  ⟦ vUnit ⟧ValTypeHidCache = Lift Unit
  ⟦ τ₁ v× τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache × ⟦ τ₂ ⟧ValTypeHidCache
  ⟦ τ₁ v+ τ₂ ⟧ValTypeHidCache = ⟦ τ₁ ⟧ValTypeHidCache ⊎ ⟦ τ₂ ⟧ValTypeHidCache

  -- This line is the only change, up to now, for the caching semantics.
  ⟦ F τ ⟧CompTypeHidCache = (Σ[ τ₁ ∈ Set ] ⟦ τ ⟧ValTypeHidCache × τ₁ )
  ⟦ σ ⇛ τ ⟧CompTypeHidCache = ⟦ σ ⟧ValTypeHidCache → ⟦ τ ⟧CompTypeHidCache
  ⟦ τ₁ Π τ₂ ⟧CompTypeHidCache = ⟦ τ₁ ⟧CompTypeHidCache × ⟦ τ₂ ⟧CompTypeHidCache

  ⟦_⟧CtxHidCache : (Γ : Context) → Set₁
  ⟦_⟧CtxHidCache = DependentList ⟦_⟧TypeHidCache

  ⟦_⟧ValCtxHidCache : (Γ : ValContext) → Set₁
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
  -- The effect of F is a writer monad of cached values (where the monoid is
  -- (isomorphic to) the free monoid over (∃ τ . τ), but we push the
  -- existentials up when pairing things)!

  -- That's what we're interpreting computations in. XXX maybe consider using
  -- monads directly. But that doesn't deal with arity.
  ⟦_⟧CompTermCache (cProduce v) ρ = , (⟦ v ⟧ValTermCache ρ , tt)

  -- For this to be enough, a lambda needs to return a produce, not to forward
  -- the underlying one (unless there are no intermediate results). The correct
  -- requirements can maybe be enforced through a linear typing discipline.

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

  -- But if we alter _into_ as described above, composing the caches works!

  ⟦_⟧CompTermCache (v₁ into2 v₂) ρ =
    let (τ₁ , (r₁ , c₁)) = ⟦ v₁ ⟧CompTermCache ρ
        (τ₂ , (r₂ , c₂)) = ⟦ v₂ ⟧CompTermCache (r₁ • ρ)
    in , (r₂ , (c₁ ,′ c₂))

  -- Note the compositionality and luck: we don't need to do anything at the
  -- cProduce time, we just need the nested into2 to do their job, because as I
  -- said intermediate results are a a writer monad. But then, do we still need
  -- to do all the other stuff? IOW, do we still need to forbid (λ x . y <- f
  -- args; g args') and replace it with (λ x . y <- f args; z <- g args'; z)?
  -- Maybe not: if we use a monad, which respects left and right identity, the
  -- two above forms are equivalent. But what about associativity? We don't have
  -- associativity with nested tuples in the middle. That's why the monad uses
  -- lists! We can also use nested tuple, as long as we don't do (a, b) but
  -- append a b (ahem, where?).

  -- In abstractions, we should start collecting all variables...

  -- Here, unlike in ⟦_⟧TermCache2, we don't need to invent an empty cache,
  -- that's moved into the handling of cProduce. This makes *the* difference for
  -- nested lambdas, where we don't need to create caches multiple times!

  ⟦_⟧CompTermCache (cAbs v) ρ x = ⟦ v ⟧CompTermCache (x • ρ)

  -- Here we see that we are in a sort of A-normal form, because the argument is
  -- a value (not quite ANF though, since values can be thunks - that is,
  -- computations which haven't been run yet, I guess. Do we have an use for
  -- that? That allows passing lambdas as arguments directly - which is fine,
  -- because producing a closure indeed does not have intermediate results!).
  ⟦_⟧CompTermCache (cApp t v) ρ = ⟦ t ⟧CompTermCache ρ (⟦ v ⟧ValTermCache ρ)
