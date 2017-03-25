module Thesis.DeriveCorrect where

open import Thesis.Lang
open import Thesis.Changes
open import Thesis.Derive
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Theorem.Groups-Nehemiah

fromtoDeriveConst : ∀ {τ} c →
  [ τ ]τ ⟦ deriveConst c ⟧Term ∅ from ⟦ c ⟧Const to ⟦ c ⟧Const
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
  ∀ {dρ ρ1 ρ2}  → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dvv v• dρρ) = dvv
fromtoDeriveVar (that x) (dvv v• dρρ) = fromtoDeriveVar x dρρ

fromtoDerive : ∀ {Γ} τ → (t : Term Γ τ) →
  {dρ : ChΓ Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ]τ (⟦ t ⟧ΔTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
fromtoDerive τ (const c) {dρ} {ρ1} dρρ rewrite ⟦ c ⟧ΔConst-rewrite ρ1 dρ = fromtoDeriveConst c
fromtoDerive τ (var x) dρρ = fromtoDeriveVar x dρρ
fromtoDerive τ (app {σ} s t) dρρ rewrite sym (fit-sound t dρρ) =
  let fromToF = fromtoDerive (σ ⇒ τ) s dρρ
  in let fromToB = fromtoDerive σ t dρρ in fromToF _ _ _ fromToB
fromtoDerive (σ ⇒ τ) (abs t) dρρ = λ dv v1 v2 dvv →
  fromtoDerive τ t (dvv v• dρρ)
