module Thesis.ANormalDiffSameLang where

open import Relation.Binary.PropositionalEquality

open import Thesis.ANormalWeaken

open import Thesis.Changes public
open import Thesis.LangChanges public

derive-var : ∀ {Γ τ} → Var Γ τ → Var (ΔΓ Γ) (Δt τ)
derive-var this = this
derive-var (that x) = that (that (derive-var x))

⟦_⟧ΔVar : ∀ {Γ τ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ x ⟧ΔVar ρ dρ = ⟦ derive-var x ⟧Var dρ

fromtoDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dvv v• dρρ) = dvv
fromtoDeriveVar (that x) (dvv v• dρρ) = fromtoDeriveVar x dρρ

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔΓ Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop Δt τ • keep τ • Γ≼ΔΓ

⟦Γ≼ΔΓ⟧ : ∀ {Γ ρ1 ρ2 dρ} → (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
  ρ1 ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ v∅ = refl
⟦Γ≼ΔΓ⟧ (dvv v• dρρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ dρρ)

fit-var : ∀ {τ Γ} → Var Γ τ → Var (ΔΓ Γ) τ
fit-var = weaken-var Γ≼ΔΓ

fit-var-sound : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ x ⟧Var ρ1 ≡ ⟦ fit-var x ⟧Var dρ
fit-var-sound x dρρ = trans
  (cong ⟦ x ⟧Var (⟦Γ≼ΔΓ⟧ dρρ))
  (sym (weaken-var-sound Γ≼ΔΓ x _))

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔΓ Γ) τ
fit = weaken-term Γ≼ΔΓ

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ t ⟧Term ρ1 ≡ ⟦ fit t ⟧Term dρ
fit-sound t dρρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ dρρ))
  (sym (weaken-term-sound Γ≼ΔΓ t _))

derive-term : ∀ {Γ τ} → Term Γ τ → Term (ΔΓ Γ) (Δt τ)
derive-term (var x) = var (derive-var x)
derive-term (lett f x t) =
  lett (fit-var f) (fit-var x)
    (lett (weaken-var (drop _ • ≼-refl) (derive-var f)) (weaken-var (drop _ • Γ≼ΔΓ) x) (
    lett this (weaken-var (drop _ • drop _ • ≼-refl) (derive-var x))
      (weaken-term (keep _ • drop _ • ≼-refl) (derive-term t))))

⟦_⟧ΔTerm : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ t ⟧ΔTerm ρ dρ = ⟦ derive-term t ⟧Term dρ


fromtoDeriveTerm : ∀ {Γ τ} → (t : Term Γ τ) →
  ch ⟦ t ⟧ΔTerm from ⟦ t ⟧Term to ⟦ t ⟧Term
-- You might think I'm going to prove the statement of fromtoDeriveTerm. In
-- fact, I'm going to prove that weakening is evil.
fromtoDeriveTerm (var x) dρ ρ1 ρ2 dρρ = fromtoDeriveVar x dρρ
fromtoDeriveTerm (lett f x t) dρ ρ1 ρ2 dρρ with ⟦ f ⟧Var ρ1 | inspect ⟦ f ⟧Var ρ1 | ⟦ x ⟧Var ρ1 | inspect ⟦ x ⟧Var ρ1 | ⟦ derive-var f ⟧Var dρ | inspect ⟦ derive-var f ⟧Var dρ
... | fv1 | [ fv1eq ] | xv1 | [ xv1eq ] | dfv1 | [ dfv1eq ] with fv1 xv1 | inspect fv1 xv1
... | fx1 | [ fx1eq ]
  rewrite sym (fit-var-sound f dρρ)
  | sym (fit-var-sound x dρρ)
  | fv1eq
  | xv1eq
  | fx1eq
  | weaken-var-sound (drop _ • ≼-refl) (derive-var f) (fx1 • dρ)
  | weaken-var-sound (drop _ • Γ≼ΔΓ) x (fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | sym (⟦Γ≼ΔΓ⟧ dρρ)
  | xv1eq
  | dfv1eq
  | weaken-var-sound (drop _ • drop _ • ≼-refl) (derive-var x) (dfv1 xv1 • fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | weaken-term-sound (keep _ • drop _ • ≼-refl) (derive-term t) (dfv1 xv1 (⟦ derive-var x ⟧Var dρ) • dfv1 xv1 • fx1 • dρ)
  | ⟦⟧-≼-refl dρ
  | sym dfv1eq
  | sym xv1eq
  | sym fx1eq
  | sym fv1eq
  =
  let fromToF = fromtoDeriveVar f dρρ
      fromToX = fromtoDeriveVar x dρρ
      fromToFX = fromToF (⟦ derive-var x ⟧Var dρ) _ _ fromToX
  in fromtoDeriveTerm t _ _ _ (fromToFX v• dρρ)

derive-fun : ∀ {Γ τ} → Fun Γ τ → Fun (ΔΓ Γ) (Δt τ)
derive-fun (term t) = term (derive-term t)
derive-fun (abs f) = abs (abs (derive-fun f))

⟦_⟧ΔFun : ∀ {Γ τ} → (t : Fun Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → Chτ τ
⟦ f ⟧ΔFun ρ dρ = ⟦ derive-fun f ⟧Fun dρ

fromtoDeriveFun : ∀ {Γ τ} → (f : Fun Γ τ) →
  ch ⟦ f ⟧ΔFun from ⟦ f ⟧Fun to ⟦ f ⟧Fun
fromtoDeriveFun (term t) = fromtoDeriveTerm t
fromtoDeriveFun (abs f) dρ ρ1 ρ2 dρρ = λ dv v1 v2 dvv → fromtoDeriveFun f (dv • v1 • dρ) (v1 • ρ1) (v2 • ρ2) (dvv v• dρρ)
