module New.Correctness where

open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality
open import Data.Product

open import New.Lang
open import New.Changes
open import New.Derive
open import New.LangChanges

-- Lemmas
alternate : ∀ {Γ} → ⟦ Γ ⟧Context → eCh Γ → ⟦ ΔΓ Γ ⟧Context
alternate {∅} ∅ ∅ = ∅
alternate {τ • Γ} (v • ρ) (dv • dρ) = dv • v • alternate ρ dρ

⟦Γ≼ΔΓ⟧ : ∀ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) →
  ρ ≡ ⟦ Γ≼ΔΓ ⟧≼ (alternate ρ dρ)
⟦Γ≼ΔΓ⟧ ∅ ∅ = refl
⟦Γ≼ΔΓ⟧ (v • ρ) (dv • dρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ ρ dρ)

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) →
  ⟦ t ⟧Term ρ ≡ ⟦ fit t ⟧Term (alternate ρ dρ)
fit-sound t ρ dρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ ρ dρ))
  (sym (weaken-sound t _))

-- The change semantics is just the semantics composed with derivation!
changeSemVar : ∀ {Γ τ} → (t : Var Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) → Cht τ
changeSemVar t ρ dρ = ⟦ deriveVar t ⟧Var (alternate ρ dρ)

changeSem : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) → Cht τ
changeSem t ρ dρ = ⟦ derive t ⟧Term (alternate ρ dρ)

-- XXX Should try to simply relate the semantics to the nil change, and prove
-- that validity can be carried over, instead of proving separately validity and
-- correctness; elsewhere this does make things simpler.

validDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) →
  validΓ ρ dρ → valid (⟦ x ⟧Var ρ) (⟦ deriveVar x ⟧Var (alternate ρ dρ))

validDeriveVar this (v • ρ) (dv • dρ) (vdv , ρdρ) = vdv
validDeriveVar (that x) (v • ρ) (dv • dρ) (vdv , ρdρ) = validDeriveVar x ρ dρ ρdρ

correctDeriveVar : ∀ {Γ τ} → (v : Var Γ τ) →
  IsDerivative ⟦ v ⟧Var (changeSemVar v)
correctDeriveVar this (v • ρ) (dv • dρ) ρdρ = refl
correctDeriveVar (that x) (v • ρ) (dv • dρ) (vdv , ρdρ) = correctDeriveVar x ρ dρ ρdρ

validDerive : ∀ {Γ τ} → (t : Term Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) → validΓ ρ dρ →
    valid (⟦ t ⟧Term ρ) (⟦ derive t ⟧Term (alternate ρ dρ))
correctDerive : ∀ {Γ τ} → (t : Term Γ τ) →
  IsDerivative ⟦ t ⟧Term (changeSem t)

semConst-rewrite : ∀ {τ Γ} (c : Const τ) (ρ : ⟦ Γ ⟧Context) dρ → changeSem (const c) ρ dρ ≡ ⟦ deriveConst c ⟧Term ∅
semConst-rewrite c ρ dρ rewrite weaken-sound {Γ₁≼Γ₂ = ∅≼Γ} (deriveConst c) (alternate ρ dρ) | ⟦∅≼Γ⟧-∅ (alternate ρ dρ) = refl

correctDeriveConst : ∀ {τ} (c : Const τ) → ⟦ c ⟧Const ≡ ⟦ c ⟧Const ⊕ ⟦ deriveConst c ⟧Term ∅
correctDeriveConst ()

validDeriveConst : ∀ {τ} (c : Const τ) → valid ⟦ c ⟧Const (⟦ deriveConst c ⟧Term ∅)
validDeriveConst ()

correctDerive (const c) ρ dρ ρdρ rewrite semConst-rewrite c ρ dρ = correctDeriveConst c
correctDerive (var x) ρ dρ ρdρ = correctDeriveVar x ρ dρ ρdρ
correctDerive (app s t) ρ dρ ρdρ rewrite sym (fit-sound t ρ dρ) =
  let
    open ≡-Reasoning
    a0 = ⟦ t ⟧Term ρ
    da0 = ⟦ derive t ⟧Term (alternate ρ dρ)
    a0da0 = validDerive t ρ dρ ρdρ
  in
    begin
      ⟦ s ⟧Term (ρ ⊕ dρ) (⟦ t ⟧Term (ρ ⊕ dρ))
    ≡⟨ correctDerive s ρ dρ ρdρ ⟨$⟩ correctDerive t ρ dρ ρdρ ⟩
      (⟦ s ⟧Term ρ ⊕ changeSem s ρ dρ) (⟦ t ⟧Term ρ ⊕ changeSem t ρ dρ)
    ≡⟨ proj₂ (validDerive s ρ dρ ρdρ a0 da0 a0da0)  ⟩
      ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ) ⊕ (changeSem s ρ dρ) (⟦ t ⟧Term ρ) (changeSem t ρ dρ)
    ∎
  where
    open import Theorem.CongApp
correctDerive (abs t) ρ dρ ρdρ = ext (λ a →
  let
    open ≡-Reasoning
    ρ1 = a • ρ
    dρ1 = nil a • dρ
    ρ1dρ1 : valid ρ1 dρ1
    ρ1dρ1 = nil-valid a , ρdρ
  in
    begin
      ⟦ t ⟧Term (a • ρ ⊕ dρ)
    ≡⟨ cong (λ a′ → ⟦ t ⟧Term (a′ • ρ ⊕ dρ)) (sym (update-nil a)) ⟩
      ⟦ t ⟧Term (ρ1 ⊕ dρ1)
    ≡⟨ correctDerive t ρ1 dρ1 ρ1dρ1 ⟩
      ⟦ t ⟧Term ρ1 ⊕ changeSem t ρ1 dρ1
    ∎)

validDerive (app s t) ρ dρ ρdρ =
  let
    f = ⟦ s ⟧Term ρ
    df = ⟦ derive s ⟧Term (alternate ρ dρ)
    v = ⟦ t ⟧Term ρ
    dv = ⟦ derive t ⟧Term (alternate ρ dρ)
    vdv = validDerive t ρ dρ ρdρ
    fdf = validDerive s ρ dρ ρdρ
    fvdfv = proj₁ (fdf v dv vdv)
  in subst (λ v′ → valid (f v) (df v′ dv)) (fit-sound t ρ dρ) fvdfv
validDerive (abs t) ρ dρ ρdρ =
  λ a da ada →
  let
    fv = ⟦ t ⟧Term (a • ρ)
    dfvdv = ⟦ derive t ⟧Term (da • a • alternate ρ dρ)
    rdr = validDerive t (a • ρ) (da • dρ) (ada , ρdρ)
    ρ1 = a ⊕ da • ρ
    dρ1 = nil (a ⊕ da) • dρ
    ρ2 = a • ρ
    dρ2 = da • dρ
    ρ1dρ1 : valid ρ1 dρ1
    ρ1dρ1 = nil-valid (a ⊕ da) , ρdρ
    ρ2dρ2 : valid ρ2 dρ2
    ρ2dρ2 = ada , ρdρ
    open ≡-Reasoning
   in
     rdr ,
     (begin
       ⟦ t ⟧Term ρ1 ⊕
       ⟦ derive t ⟧Term (alternate ρ1 dρ1)
      ≡⟨ sym ( correctDerive t ρ1 dρ1 ρ1dρ1) ⟩
       ⟦ t ⟧Term (ρ1 ⊕ dρ1)
      ≡⟨⟩
       ⟦ t ⟧Term (a ⊕ da ⊕ (nil (a ⊕ da)) • ρ ⊕ dρ)
      ≡⟨ cong (λ a′ → ⟦ t ⟧Term (a′ • ρ ⊕ dρ)) (update-nil (a ⊕ da)) ⟩
       ⟦ t ⟧Term (a ⊕ da • ρ ⊕ dρ)
      ≡⟨ correctDerive t ρ2 dρ2 ρ2dρ2 ⟩
        ⟦ t ⟧Term (a • ρ) ⊕ ⟦ derive t ⟧Term (da • a • alternate ρ dρ)
      ∎)
validDerive (var x) ρ dρ ρdρ = validDeriveVar x ρ dρ ρdρ
validDerive (const c) ρ dρ ρdρ rewrite semConst-rewrite c ρ dρ = validDeriveConst c
