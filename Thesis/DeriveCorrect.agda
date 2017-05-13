module Thesis.DeriveCorrect where

open import Thesis.Lang
open import Thesis.Changes
open import Thesis.LangChanges
open import Thesis.Derive

open import Relation.Binary.PropositionalEquality

open import Theorem.Groups-Nehemiah

fromtoDeriveConst : ∀ {τ : Type} (c : Const τ) →
  ch ⟦ c ⟧ΔConst from ⟦ c ⟧Const to ⟦ c ⟧Const
fromtoDeriveConst unit = tt
fromtoDeriveConst (lit n) = right-id-int n
fromtoDeriveConst plus da a1 a2 daa db b1 b2 dbb rewrite sym daa | sym dbb = sym (mn·pq=mp·nq {a1} {da} {b1} {db})
fromtoDeriveConst minus da a1 a2 daa db b1 b2 dbb rewrite sym daa | sym dbb | sym (-m·-n=-mn {b1} {db}) = sym (mn·pq=mp·nq {a1} {da} { - b1} { - db})
fromtoDeriveConst cons da a1 a2 daa db b1 b2 dbb = daa , dbb
fromtoDeriveConst fst (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = daa
fromtoDeriveConst snd (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = dbb
fromtoDeriveConst linj da a1 a2 daa = sft₁ daa
fromtoDeriveConst rinj db b1 b2 dbb = sft₂ dbb
fromtoDeriveConst match .(inj₁ (inj₁ _)) .(inj₁ _) .(inj₁ _) (sft₁ daa) df f1 f2 dff dg g1 g2 dgg = dff _ _ _ daa
fromtoDeriveConst match .(inj₁ (inj₂ _)) .(inj₂ _) .(inj₂ _) (sft₂ dbb) df f1 f2 dff dg g1 g2 dgg = dgg _ _ _ dbb
fromtoDeriveConst match .(inj₂ (inj₂ b2)) .(inj₁ a1) .(inj₂ b2) (sftrp₁ a1 b2) df f1 f2 dff dg g1 g2 dgg
 rewrite changeMatchSem-lem1 f1 df g1 dg a1 b2
 | sym (fromto→⊕ dg g1 g2 dgg) = ⊝-fromto (f1 a1) ((g1 ⊕ dg) b2)
fromtoDeriveConst match .(inj₂ (inj₁ a2)) .(inj₂ b1) .(inj₁ a2) (sftrp₂ b1 a2) df f1 f2 dff dg g1 g2 dgg
  rewrite changeMatchSem-lem2 f1 df g1 dg b1 a2
  | sym (fromto→⊕ df f1 f2 dff)
   = ⊝-fromto (g1 b1) ((f1 ⊕ df) a2)

fromtoDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dvv v• dρρ) = dvv
fromtoDeriveVar (that x) (dvv v• dρρ) = fromtoDeriveVar x dρρ

fromtoDeriveBase : ∀ {Γ} τ → (t : Term Γ τ) →
  ch ⟦ t ⟧ΔTerm from ⟦ t ⟧Term to ⟦ t ⟧Term
fromtoDeriveBase τ (const c) dρ ρ1 ρ2 dρρ rewrite ⟦ c ⟧ΔConst-rewrite ρ1 dρ = fromtoDeriveConst c
fromtoDeriveBase τ (var x) dρ ρ1 ρ2 dρρ = fromtoDeriveVar x dρρ
fromtoDeriveBase τ (app {σ} s t) dρ ρ1 ρ2 dρρ rewrite sym (fit-sound t dρρ) =
  let fromToF = fromtoDeriveBase (σ ⇒ τ) s _ _ _ dρρ
  in let fromToB = fromtoDeriveBase σ t _ _ _ dρρ in fromToF _ _ _ fromToB
fromtoDeriveBase (σ ⇒ τ) (abs t) dρ ρ1 ρ2 dρρ = λ dv v1 v2 dvv →
   fromtoDeriveBase τ t _ _ _ (dvv v• dρρ)
fromtoDerive : ∀ {Γ} τ → (t : Term Γ τ) →
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ t ⟧ΔTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
fromtoDerive τ t dρρ = fromtoDeriveBase τ t _ _ _ dρρ

-- Getting to the original equation 1 from PLDI'14.

correctDeriveOplus : ∀ {Γ} τ → (t : Term Γ τ) →
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
     (⟦ t ⟧Term ρ1) ⊕ (⟦ t ⟧ΔTerm ρ1 dρ) ≡ (⟦ t ⟧Term ρ2)
correctDeriveOplus τ t dρρ = fromto→⊕ _ _ _ (fromtoDerive τ t dρρ)

open import Thesis.LangOps

correctDeriveOplusτ : ∀ {Γ} τ → (t : Term Γ τ)
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
     (⟦ app₂ (oplusτo τ) (fit t) (derive t) ⟧Term dρ) ≡ (⟦ t ⟧Term ρ2)
correctDeriveOplusτ τ t {dρ = dρ} {ρ1 = ρ1} dρρ
  rewrite oplusτ-equiv _ dρ _ (⟦ fit t ⟧Term dρ) (⟦ derive t ⟧Term dρ)
  | sym (fit-sound t dρρ)
  = correctDeriveOplus τ t dρρ

deriveGivesDerivative : ∀ {Γ} σ τ → (f : Term Γ (σ ⇒ τ)) (a : Term Γ σ)→
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
     (⟦ app f a ⟧Term ρ1) ⊕ (⟦ app f a ⟧ΔTerm ρ1 dρ) ≡ (⟦ app f a ⟧Term ρ2)
deriveGivesDerivative σ τ f a dρρ = correctDeriveOplus τ (app f a) dρρ

deriveGivesDerivative₂ : ∀ {Γ} σ τ → (f : Term Γ (σ ⇒ τ)) (a : Term Γ σ) →
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
     (⟦ app₂ (oplusτo τ) (fit (app f a)) (app₂ (derive f) (fit a) (derive a)) ⟧Term dρ) ≡ (⟦ app f a ⟧Term ρ2)
deriveGivesDerivative₂ σ τ f a dρρ = correctDeriveOplusτ τ (app f a) dρρ

-- Proof of the original equation 1 from PLDI'14. The original was restricted to
-- closed terms. This is a generalization, because it holds also for open terms,
-- *as long as* the environment change is a nil change.
eq1 : ∀ {Γ} σ τ →
  {nilρ : ChΓ Γ} {ρ : ⟦ Γ ⟧Context} → [ Γ ]Γ nilρ from ρ to ρ →
  ∀ (f : Term Γ (σ ⇒ τ)) (a : Term Γ σ) (da : Term (ΔΓ Γ) (Δt σ)) →
  (daa : [ σ ]τ (⟦ da ⟧Term nilρ) from (⟦ a ⟧Term ρ) to (⟦ a ⟧Term ρ ⊕ ⟦ da ⟧Term nilρ)) →
    ⟦ app₂ (oplusτo τ) (fit (app f a)) (app₂ (derive f) (fit a) da) ⟧Term nilρ ≡ ⟦ app (fit f) (app₂ (oplusτo σ) (fit a) da) ⟧Term nilρ
eq1 σ τ {nilρ} {ρ} dρρ f a da daa
  rewrite
    oplusτ-equiv _ nilρ _ (⟦ fit (app f a) ⟧Term nilρ) (⟦ (app₂ (derive f) (fit a) da) ⟧Term nilρ)
  | sym (fit-sound f dρρ)
  | oplusτ-equiv _ nilρ _ (⟦ fit a ⟧Term nilρ) (⟦ da ⟧Term nilρ)
  | sym (fit-sound a dρρ)
  = fromto→⊕ (⟦ f ⟧ΔTerm ρ nilρ (⟦ a ⟧Term ρ) (⟦ da ⟧Term nilρ)) _ _
    (fromtoDerive _ f dρρ (⟦ da ⟧Term nilρ) (⟦ a ⟧Term ρ)
      (⟦ a ⟧Term ρ ⊕ ⟦ da ⟧Term nilρ) daa)
