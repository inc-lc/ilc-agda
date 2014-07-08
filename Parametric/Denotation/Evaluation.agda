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
  --   ⟦ terms ⟧Terms ρ = map (λ t → ⟦ t ⟧Term ρ) terms
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

  ⟦_⟧CtxHidCache : (Γ : Context) → Set₁
  ⟦_⟧CtxHidCache = DependentList ⟦_⟧TypeHidCache

  -- It's questionable that this is not polymorphic enough.
  ⟦_⟧VarHidCache : ∀ {Γ τ} → Var Γ τ → ⟦ Γ ⟧CtxHidCache → ⟦ τ ⟧TypeHidCache
  ⟦ this ⟧VarHidCache (v • ρ) = v
  ⟦ that x ⟧VarHidCache (v • ρ) = ⟦ x ⟧VarHidCache ρ


  -- The mutual recursion looks like a fold on exponentials, where you need to define the function and the inverse at the same time.
  -- Indeed, both functions seem structurally recursive on τ.
  dropCache : ∀ {τ} → ⟦ τ ⟧TypeHidCache → ⟦ τ ⟧
  extend : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧TypeHidCache

  dropCache {base ι} v = lower v
  dropCache {σ ⇒ τ} v x = dropCache (proj₁ (proj₂ (v (extend x))))

  extend {base ι} v = lift v
  extend {σ ⇒ τ} v = λ x → ⊤ , (extend (v (dropCache x)) , tt)

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
  ⟦_⟧TermCache2 (app s t) ρ = proj₁ (proj₂ ((⟦ s ⟧TermCache2 ρ) (⟦ t ⟧TermCache2 ρ)))
  -- Provide an empty cache!
  ⟦_⟧TermCache2 (abs t) ρ x = ⊤ , (⟦ t ⟧TermCache2 (x • ρ) , tt)
