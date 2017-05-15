module Thesis.ANormalCTerm where

open import Thesis.ANormalDTerm

data CType : Set where
  cache : CType
  input : Type → CType

open import Data.Product

⟦_⟧CType : CType → Set
-- This is a lie, since we might need to store more complex values in there,
-- including caches...
⟦ cache ⟧CType = Σ[ τ ∈ Type ] ⟦ τ ⟧Type
-- However, this is more correct but is not recognized as terminating.
-- ⟦ cache ⟧CType = Σ[ τ ∈ CType ] ⟦ τ ⟧CType
-- Finally, this definition is too impredicative for Agda to accept it. If
-- ⟦_⟧CType lived in Set₁, it could still not contain values of itself.
-- ⟦ cache ⟧CType = Σ[ S ∈ Set ] S
⟦ input τ ⟧CType = ⟦ τ ⟧Type

-- Maybe step-indexing to the rescue. Really not sure how to step-index the theorems?
-- Maybe compute the needed index while running the base program?
open import Data.Nat
⟦_⟧CTypeN : CType → ℕ → Set
⟦ input τ ⟧CTypeN n = ⟦ τ ⟧Type
⟦ cache ⟧CTypeN 0 = ⊤
⟦ cache ⟧CTypeN (suc n) = Σ[ τ ∈ CType ] ⟦ τ ⟧CTypeN n

open import Base.Syntax.Context CType using () renaming (Context to CCtx)
open import Base.Denotation.Environment CType ⟦_⟧CType using () renaming (⟦_⟧Context to ⟦_⟧CCtx) 

data CTerm : (C CFin : CCtx) (Δ : Context) (τ : Type) → Set where
  cvar : ∀ {CFin Δ τ} (x : Var Δ τ) →
    CTerm CFin CFin Δ τ
  clett : ∀ {C CFin Δ τ σ τ₁} →
    (f : Var Δ (σ ⇒ τ₁)) →
    (x : Var Δ σ) →
    -- XXX pretend we only store integers. We should instead use a separate type of caches.
    (ct : CTerm (cache • C) CFin (τ₁ • Δ) τ) →
    CTerm C CFin Δ τ

-- Rather bogus: the contexts are unchanged. Our functions have a different type here!
⟦_⟧CTerm : ∀ {C CFin Δ τ} → CTerm C CFin Δ τ → ⟦ Δ ⟧Context → ⟦ C ⟧CCtx → (⟦ τ ⟧Type × ⟦ CFin ⟧CCtx)
⟦ cvar x ⟧CTerm ρ c = ⟦ x ⟧Var ρ , c
⟦ clett f x ct ⟧CTerm ρ c =
  let v = ⟦ f ⟧Var ρ (⟦ x ⟧Var ρ)
  in ⟦ ct ⟧CTerm (v • ρ) ((_ , v) • c)

cache-term-cps : ∀ {Δ σ} {Z : Set} → (t : Term Δ σ) → ∀ C → (∀ CFin → CTerm C CFin Δ σ → Z) → Z
cache-term-cps (var x) C k = k C (cvar x)
cache-term-cps (lett f x t) C k = cache-term-cps t (cache • C) (λ CFin ct → k CFin (clett f x ct))

cache-term-Σ : ∀ {Δ σ} → (t : Term Δ σ) → ∀ C → Σ[ CFin ∈ CCtx ] CTerm C CFin Δ σ
cache-term-Σ (var x) CFin = CFin , cvar x
cache-term-Σ (lett f x t) C =
  let CFin , ct = cache-term-Σ t (cache • C)
  in CFin , clett f x ct
-- clett f x (cache-term t)
-- -- ⟦_⟧CType : Type → Context → Set
-- -- ⟦ σ ⇒ τ ⟧CType C = {!!}
-- -- ⟦ pair σ τ ⟧CType C = {!!}
-- -- ⟦ sum σ τ ⟧CType C = {!!}
-- -- ⟦ unit ⟧CType C = ⟦ unit ⟧Type × ⟦ C ⟧Context
-- -- ⟦ int ⟧CType C = {!!}

-- data CFun (C CFin : Context) : (Δ : Context) (τ : Type) → Set where
--   cabs : ∀ {σ τ Δ} → CFun (σ • C) CFin (σ • Δ) τ → CFun C CFin Δ (σ ⇒ τ)
--   cterm : ∀ {τ Δ} → CTerm C CFin Δ τ → CFun C CFin Δ τ

-- -- Ouch, this is a lie.... We'd need a different type structure.
-- ⟦_⟧CFun : ∀ {C CFin Δ τ} → CFun C CFin Δ τ → ⟦ Δ ⟧Context → ⟦ C ⟧Context → (⟦ τ ⟧Type × ⟦ CFin ⟧Context)
-- ⟦ cabs cf ⟧CFun ρ c = (λ v → proj₁ (⟦ cf ⟧CFun (v • ρ) (v • c))) , {!!}
-- ⟦ cterm ct ⟧CFun ρ c = ⟦ ct ⟧CTerm ρ c

-- ⟦_⟧CFun2 : ∀ {C CFin Δ σ τ} → CFun C CFin Δ (σ ⇒ τ) → ⟦ Δ ⟧Context → ⟦ C ⟧Context → ⟦ σ ⟧Type → (⟦ τ ⟧Type × ⟦ CFin ⟧Context)
-- ⟦ cabs cf ⟧CFun2 ρ c = λ v → (⟦ cf ⟧CFun (v • ρ) (v • c)) 
-- -- (λ v → proj₁ (⟦ cf ⟧CFun (v • ρ) (v • c))) , {!!}
-- ⟦ cterm ct ⟧CFun2 ρ c = {! ⟦ ct ⟧CTerm ρ c!}

-- Above we run into the usual problems with nested caching.
data CFunR (C CFin : CCtx) : (Δ : Context) (τ : Type) → Set where
  cabsterm : ∀ {σ τ Δ} → CTerm (input σ • C) CFin (σ • Δ) τ → CFunR C CFin Δ (σ ⇒ τ)

⟦_⟧CFunR : ∀ {C CFin Δ σ τ} → CFunR C CFin Δ (σ ⇒ τ) → ⟦ Δ ⟧Context → ⟦ C ⟧CCtx → ⟦ σ ⟧Type → (⟦ τ ⟧Type × ⟦ CFin ⟧CCtx)
⟦ cabsterm ct ⟧CFunR ρ c v = ⟦ ct ⟧CTerm (v • ρ) (v • c)

-- IMPORTANT: Here we need different change types:
ΔτC : Type → Type
ΔτC (σ ⇒ τ) = ΔτC σ ⇒ ΔτC τ
ΔτC unit = unit
ΔτC int = int
ΔτC (pair σ τ) = pair (ΔτC σ) (ΔτC τ)
ΔτC (sum σ τ) = sum (sum (ΔτC σ) (ΔτC τ)) (sum σ τ)

ΔΔC : Context → Context
ΔΔC ∅ = ∅
ΔΔC (τ • Γ) = ΔτC τ • ΔΔC Γ

derive-dcvar : ∀ {Δ σ} → (x : Var Δ σ) → Var (ΔΔC Δ) (ΔτC σ)
derive-dcvar this = this
derive-dcvar (that x) = that (derive-dcvar x)

-- REAL BULLSHIT
-- XXX Not accounted for: derivatives also take caches!
-- C: accumulated caches. CFin: the ones we have at the end.
data CDTerm : (C CFin : CCtx) (Δ : Context) (τ : Type) → Set where
  cdvar : ∀ {CFin Δ τ} (x : Var (ΔΔC Δ) (ΔτC τ)) →
    CDTerm CFin CFin Δ τ
  cdlett : ∀ {C CFin Δ τ σ τ₁} →
    -- Here, we also need to pass (and update) the RIGHT cache. Otherwise
    -- there's no point.
    (df : Var (ΔΔC Δ) (ΔτC (σ ⇒ τ₁))) →
    (dx : Var (ΔΔC Δ) (ΔτC σ)) →
    (dt : CDTerm (cache • C) CFin (τ₁ • Δ) τ) →
    CDTerm C CFin Δ τ

der-cache-term-Σ : ∀ {Δ σ} → (t : Term Δ σ) → ∀ C → Σ[ CFin ∈ CCtx ] CDTerm C CFin Δ σ
der-cache-term-Σ (var x) CFin = CFin , cdvar (derive-dcvar x)
der-cache-term-Σ (lett f x t) C =
  let CFin , cdt = der-cache-term-Σ t (cache • C)
  in CFin , cdlett (derive-dcvar f) (derive-dcvar x) cdt

--⟦_⟧DTerm : ∀ {Δ τ} → DTerm Δ τ → ⟦ Δ ⟧Context → ⟦ ΔΔ Δ ⟧Context → ⟦ Δt τ ⟧Type
⟦_⟧CDTerm : ∀ {C CFin Δ τ} → CDTerm C CFin Δ τ → ⟦ ΔΔC Δ ⟧Context → ⟦ C ⟧CCtx → (⟦ ΔτC τ ⟧Type × ⟦ CFin ⟧CCtx)
⟦ cdvar x ⟧CDTerm dρ c = ⟦ x ⟧Var dρ , c
⟦ cdlett df dx cdt ⟧CDTerm dρ c =
  let dv = ⟦ df ⟧Var dρ (⟦ dx ⟧Var dρ)
  in ⟦ cdt ⟧CDTerm (dv • dρ) ((_ , dv) • c) 

-- ⟦ cvar x ⟧CTerm ρ c = ⟦ x ⟧Var ρ , c
-- ⟦ clett f x ct ⟧CTerm ρ c =
--   let v = ⟦ f ⟧Var ρ (⟦ x ⟧Var ρ)
--   in ⟦ ct ⟧CTerm (v • ρ) ((_ , v) • c)

-- At the top, C is empty.
data CDFun (C CFin : CCtx) : (Δ : Context) (τ : Type) → Set where
  cdabs : ∀ {σ τ Δ} → CDFun (input σ • C) CFin (σ • Δ) τ → CDFun C CFin Δ (σ ⇒ τ)
  cdterm : ∀ {τ Δ} → CDTerm C CFin Δ τ → CDFun C CFin Δ τ

data CDFunR (C CFin : CCtx) : (Δ : Context) (τ : Type) → Set where
  cdabsterm : ∀ {σ τ Δ} → CDTerm (input σ • C) CFin (σ • Δ) τ → CDFunR C CFin Δ (σ ⇒ τ)
