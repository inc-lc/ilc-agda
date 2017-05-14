module Thesis.ANormalDTerm where

open import Thesis.ANormal

{-
Try defining an alternative syntax for differential terms. We'll need this for
cache terms. Maybe?

Options:

1. use standard untyped lambda calculus as a target language. This requires much
more weakening in the syntax, which is a nuisance in proofs. Maybe use de Bruijn
levels instead?

2. use a specialized syntax as a target language.

3. use separate namespaces, environments, and so on?

Also, caching uses quite a bit of sugar on top of lambda calculus, with pairs
and what not.
-}

{-
-- To define an alternative syntax for the derivation output, let's remember that:
derive (var x) = dvar dx
derive (let y = f x in t) = let y = f x ; dy = df x dx in derive t
-}

-- Attempt 1 leads to function calls in datatype indexes. That's very very bad!
module Try1 where

-- data DTerm : (Γ : Context) (τ : Type) → Set where
--   dvar : ∀ {Γ τ} (x : Var Γ τ) →
--     DTerm (ΔΓ Γ) (Δt τ)
--   dlett : ∀ {Γ σ τ₁ τ} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → DTerm (Δt τ₁ • τ₁ • ΔΓ Γ) (Δt τ) → DTerm (ΔΓ Γ) (Δt τ)

-- derive-dterm : ∀ {Γ τ} → Term Γ τ → DTerm (ΔΓ Γ) (Δt τ)
-- derive-dterm (var x) = dvar x
-- derive-dterm (lett f x t) = dlett f x (derive-dterm t)

-- Case split on dt FAILS!
-- ⟦_⟧DTerm : ∀ {Γ τ} → DTerm (ΔΓ Γ) (Δt τ) → ⟦ ΔΓ Γ ⟧Context → ⟦ Δt τ ⟧Type
-- ⟦ dt ⟧DTerm ρ = {!dt!}

ΔΔ : Context → Context
ΔΔ ∅ = ∅
ΔΔ (τ • Γ) = Δt τ • ΔΔ Γ
Δτ = Δt

ChΔ : ∀ (Δ : Context) → Set
ChΔ Δ = ⟦ ΔΔ Δ ⟧Context

-- changeStructureΔ : ∀ Δ → ChangeStructure ⟦ Δ ⟧Context
-- changeStructureΔ = {!!}
-- ch_from_to_ {{changeStructureΔ Δ}}
-- [_]Δ_from_to_ : ∀ Δ → ChΔ Δ → (ρ1 ρ2 : ⟦ Δ ⟧Context) → Set
-- [ ∅ ]Δ ∅ from ∅ to ∅ = ⊤
-- [ τ • Δ ]Δ dv • dρ from v1 • ρ1 to (v2 • ρ2) = [ τ ]τ dv from v1 to v2 × [ Δ ]Δ dρ from ρ1 to ρ2

-- Δ is bound to the change type! Not good!
data [_]Δ_from_to_ : ∀ Δ → ChΔ Δ → (ρ1 ρ2 : ⟦ Δ ⟧Context) → Set where
  v∅ : [ ∅ ]Δ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Δ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ]τ dv from v1 to v2) →
    (dρρ : [ Δ ]Δ dρ from ρ1 to ρ2) →
    [ τ • Δ ]Δ (dv • dρ) from (v1 • ρ1) to (v2 • ρ2)

module Try3 where
  derive-dvar : ∀ {Δ σ} → (x : Var Δ σ) → Var (ΔΔ Δ) (Δτ σ)
  derive-dvar this = this
  derive-dvar (that x) = that (derive-dvar x)

  fromtoDeriveDVar : ∀ {Δ τ} → (x : Var Δ τ) →
    ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ derive-dvar x ⟧Var dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
  fromtoDeriveDVar this (dvv v• dρρ) = dvv
  fromtoDeriveDVar (that x) (dvv v• dρρ) = fromtoDeriveDVar x dρρ

  -- A DTerm evaluates in normal context Δ, change context (ΔΔ Δ), and produces
  -- a result of type (Δt τ).
  data DTerm : (Δ : Context) (τ : Type) → Set where
    dvar : ∀ {Δ τ} (x : Var (ΔΔ Δ) (Δt τ)) →
      DTerm Δ τ
    dlett : ∀ {Δ τ σ τ₁} →
      (f : Var Δ (σ ⇒ τ₁)) →
      (x : Var Δ σ) →
      (t : Term (τ₁ • Δ) τ) →
      (df : Var (ΔΔ Δ) (Δτ (σ ⇒ τ₁))) →
      (dx : Var (ΔΔ Δ) (Δτ σ)) →
      (dt : DTerm (τ₁ • Δ) τ) →
      DTerm Δ τ

  data DFun (Δ : Context) : (τ : Type) → Set where
    dterm : ∀ {τ} → DTerm Δ τ → DFun Δ τ
    dabs : ∀ {σ τ} → DFun (σ • Δ) τ → DFun Δ (σ ⇒ τ)

  derive-dterm : ∀ {Δ σ} → (t : Term Δ σ) → DTerm Δ σ
  derive-dterm (var x) = dvar (derive-dvar x)
  derive-dterm (lett f x t) =
    dlett f x t (derive-dvar f) (derive-dvar x) (derive-dterm t)

  ⟦_⟧DTerm : ∀ {Δ τ} → DTerm Δ τ → ⟦ Δ ⟧Context → ⟦ ΔΔ Δ ⟧Context → ⟦ Δt τ ⟧Type
  ⟦ dvar x ⟧DTerm ρ dρ = ⟦ x ⟧Var dρ
  ⟦ dlett f x t df dx dt ⟧DTerm ρ dρ =
    let v = (⟦ x ⟧Var ρ)
    in
      ⟦ dt ⟧DTerm
        (⟦ f ⟧Var ρ v • ρ)
        (⟦ df ⟧Var dρ v (⟦ dx ⟧Var dρ) • dρ)

  fromtoDeriveDTerm : ∀ {Δ τ} → (t : Term Δ τ) →
    ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ derive-dterm t ⟧DTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
  fromtoDeriveDTerm (var x) dρρ = fromtoDeriveDVar x dρρ
  fromtoDeriveDTerm (lett f x t) dρρ =
    let fromToF = fromtoDeriveDVar f dρρ
        fromToX = fromtoDeriveDVar x dρρ
        fromToFX = fromToF _ _ _ fromToX
    in fromtoDeriveDTerm t (fromToFX v• dρρ)

  derive-dfun : ∀ {Δ σ} → (t : Fun Δ σ) → DFun Δ σ
  derive-dfun (term t) = dterm (derive-dterm t)
  derive-dfun (abs f) = dabs (derive-dfun f)

  ⟦_⟧DFun : ∀ {Δ τ} → DFun Δ τ → ⟦ Δ ⟧Context → ⟦ ΔΔ Δ ⟧Context → ⟦ Δt τ ⟧Type
  ⟦ dterm t ⟧DFun = ⟦ t ⟧DTerm
  ⟦ dabs df ⟧DFun ρ dρ = λ v dv → ⟦ df ⟧DFun (v • ρ) (dv • dρ)

  fromtoDeriveDFun : ∀ {Δ τ} → (f : Fun Δ τ) →
    ∀ {dρ ρ1 ρ2} → [ Δ ]Δ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ derive-dfun f ⟧DFun ρ1 dρ) from (⟦ f ⟧Fun ρ1) to (⟦ f ⟧Fun ρ2)
  fromtoDeriveDFun (term t) = fromtoDeriveDTerm t
  fromtoDeriveDFun (abs f) dρρ = λ dv v1 v2 dvv → fromtoDeriveDFun f (dvv v• dρρ)

module Try2 where
  -- This is literally isomorphic to the source type :-| derivation is part of erasure...
  data DTerm : (Γ : Context) (τ : Type) → Set where
    dvar : ∀ {Γ τ} (x : Var Γ τ) →
      DTerm Γ τ
  --  dlett : ∀ {Γ σ τ₁ τ} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) → DTerm (Δt τ₁ • τ₁ • ΔΓ Γ) (Δt τ) → DTerm (ΔΓ Γ) (Δt τ)

    dlett : ∀ {Γ τ σ τ₁} → (f : Var Γ (σ ⇒ τ₁)) → (x : Var Γ σ) →
      DTerm (τ₁ • Γ) τ →
      DTerm Γ τ

  derive-dterm : ∀ {Γ τ} → Term Γ τ → DTerm Γ τ
  derive-dterm (var x) = dvar x
  derive-dterm (lett f x t) = dlett f x (derive-dterm t)

  -- Incremental semantics over terms. Same results as base semantics over change
  -- terms. But less weakening.
  ⟦_⟧DTerm : ∀ {Γ τ} → DTerm Γ τ → ⟦ ΔΓ Γ ⟧Context → ⟦ Δt τ ⟧Type
  ⟦ dvar x ⟧DTerm dρ = ⟦ derive-var x ⟧Var dρ
  ⟦ dlett f x dt ⟧DTerm dρ =
    let ρ = ⟦ Γ≼ΔΓ ⟧≼ dρ
    in ⟦ dt ⟧DTerm
      ( ⟦ derive-var f ⟧Var dρ (⟦ x ⟧Var ρ) (⟦ derive-var x ⟧Var dρ)
      • ⟦ f ⟧Var ρ (⟦ x ⟧Var ρ)
      • dρ)
