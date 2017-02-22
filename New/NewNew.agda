module New.NewNew where

open import New.Changes
open import New.LangChanges
open import New.Lang
open import New.Types
open import New.Derive

[_]_from_to_ : ∀ (τ : Type) → (dv : Cht τ) → (v1 v2 : ⟦ τ ⟧Type) → Set
[ σ ⇒ τ ] df from f1 to f2 =
  ∀ (da : Cht σ) (a1 a2 : ⟦ σ ⟧Type) →
  [ σ ] da from a1 to a2 → [ τ ] df a1 da from f1 a1 to f2 a2
[ int ] dv from v1 to v2 = v2 ≡ v1 + dv
[ pair σ τ ] (da , db) from (a1 , b1) to (a2 , b2) = [ σ ] da from a1 to a2 × [ τ ] db from b1 to b2

[_]Γ_from_to_ : ∀ Γ → eCh Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set
[ ∅ ]Γ ∅ from ∅ to ∅ = ⊤
[ τ • Γ ]Γ (dv • v1' • dρ) from (v1 • ρ1) to (v2 • ρ2) =
   [ τ ] dv from v1 to v2 × v1 ≡ v1' × [ Γ ]Γ dρ from ρ1 to ρ2

⟦Γ≼ΔΓ⟧ : ∀ {Γ} (ρ1 ρ2 : ⟦ Γ ⟧Context) (dρ : eCh Γ) → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ρ1 ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ ∅ ∅ ∅ tt = refl
⟦Γ≼ΔΓ⟧ (v1 • ρ1) (v2 • ρ2) (dv • .v1 • dρ) (dvv , refl , dρρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ ρ1 ρ2 dρ dρρ)

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  (ρ1 ρ2 : ⟦ Γ ⟧Context) (dρ : eCh Γ) → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ t ⟧Term ρ1 ≡ ⟦ fit t ⟧Term dρ
fit-sound t ρ1 ρ2 dρ dρρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ ρ1 ρ2 dρ dρρ))
  (sym (weaken-sound t _))

fromtoDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  (dρ : eCh Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context) → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ] (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dv • .v1 • dρ) (v1 • ρ1) (v2 • ρ2) (dvv , refl , dρρ) = dvv
fromtoDeriveVar (that x) (dv • .v1 • dρ) (v1 • ρ1) (v2 • ρ2) (dvv , refl , dρρ) = fromtoDeriveVar x dρ ρ1 ρ2 dρρ

fromtoDeriveConst : ∀ {τ} c →
  [ τ ] ⟦ deriveConst c ⟧Term ∅ from ⟦ c ⟧Const to ⟦ c ⟧Const
fromtoDeriveConst plus da a1 a2 daa db b1 b2 dbb rewrite daa | dbb = mn·pq=mp·nq {a1} {da} {b1} {db}
fromtoDeriveConst minus da a1 a2 daa db b1 b2 dbb rewrite daa | dbb | sym (-m·-n=-mn {b1} {db}) = mn·pq=mp·nq {a1} {da} { - b1} { - db}
fromtoDeriveConst cons da a1 a2 daa db b1 b2 dbb = daa , dbb
fromtoDeriveConst fst (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = daa
fromtoDeriveConst snd (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = dbb

fromtoDerive : ∀ {Γ} τ → (t : Term Γ τ) →
  {dρ : eCh Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ] (⟦ t ⟧ΔTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
fromtoDerive τ (const c) {dρ} {ρ1} dρρ rewrite ⟦ c ⟧ΔConst-rewrite ρ1 dρ = fromtoDeriveConst c
fromtoDerive τ (var x) dρρ = fromtoDeriveVar x _ _ _ dρρ
fromtoDerive τ (app {σ} s t) {dρ} {ρ1} {ρ2} dρρ rewrite sym (fit-sound t ρ1 ρ2 dρ dρρ) =
  let fromToF = fromtoDerive (σ ⇒ τ) s dρρ
  in let fromToB = fromtoDerive σ t dρρ in fromToF _ _ _ fromToB
fromtoDerive (σ ⇒ τ) (abs t) dρρ = λ da a1 a2 daa →
  fromtoDerive τ t (daa , refl , dρρ)
