module New.Correctness where

open import Relation.Binary.PropositionalEquality
open import Postulate.Extensionality
open import Data.Product
open import Data.Sum
open import Data.Unit

open import New.Lang
open import New.Changes
open import New.Derive
open import New.LangChanges
open import New.LangOps

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

changeSemConst : ∀ {τ} (c : Const τ) → Cht τ
changeSemConst c = ⟦ deriveConst c ⟧Term ∅

changeSemConst-rewrite : ∀ {τ Γ} (c : Const τ) (ρ : ⟦ Γ ⟧Context) dρ → changeSem (const c) ρ dρ ≡ changeSemConst c
changeSemConst-rewrite c ρ dρ rewrite weaken-sound {Γ₁≼Γ₂ = ∅≼Γ} (deriveConst c) (alternate ρ dρ) | ⟦∅≼Γ⟧-∅ (alternate ρ dρ) = refl

validDeriveConst : ∀ {τ} (c : Const τ) → valid ⟦ c ⟧Const (changeSemConst c)
correctDeriveConst : ∀ {τ} (c : Const τ) → ⟦ c ⟧Const ≡ ⟦ c ⟧Const ⊕ (changeSemConst c)
correctDeriveConst plus = ext (λ m → ext (lemma m))
  where
    open import Data.Integer
    open import Theorem.Groups-Nehemiah
    lemma : ∀ m n → m + n ≡ m + n + (m + - m + (n + - n))
    lemma m n rewrite right-inv-int m | right-inv-int n | right-id-int (m + n) = refl

correctDeriveConst minus = ext (λ m → ext (λ n → lemma m n))
  where
    open import Data.Integer
    open import Theorem.Groups-Nehemiah
    lemma : ∀ m n → m - n ≡ m - n + (m + - m - (n + - n))
    lemma m n rewrite right-inv-int m | right-inv-int n | right-id-int (m - n) = refl
correctDeriveConst cons = ext (λ v1 → ext (λ v2 → sym (update-nil (v1 , v2))))
correctDeriveConst fst = ext (λ vp → sym (update-nil (proj₁ vp)))
correctDeriveConst snd = ext (λ vp → sym (update-nil (proj₂ vp)))
correctDeriveConst linj = ext (λ va → sym (cong inj₁ (update-nil va)))
correctDeriveConst rinj = ext (λ vb → sym (cong inj₂ (update-nil vb)))

open import New.Equivalence
validDeriveConst {τ = t1 ⇒ t2 ⇒ pair .t1 .t2} cons = binary-valid (λ a da ada b db bdb → (ada , bdb)) dcons-eq
  where
    open BinaryValid ⟦ cons {t1} {t2} ⟧Const (changeSemConst cons)
    dcons-eq : binary-valid-eq-hp
    dcons-eq a da ada b db bdb rewrite update-nil (a ⊕ da) | update-nil (b ⊕ db) = refl
validDeriveConst fst (a , b) (da , db) (ada , bdb) = ada , update-nil (a ⊕ da)
validDeriveConst snd (a , b) (da , db) (ada , bdb) = bdb , update-nil (b ⊕ db)

validDeriveConst plus = binary-valid (λ a da ada b db bdb → tt) dplus-eq
  where
    open import Data.Integer
    open import Theorem.Groups-Nehemiah
    open BinaryValid ⟦ plus ⟧Const (changeSemConst plus)
    dplus-eq : binary-valid-eq-hp
    dplus-eq a da ada b db bdb rewrite right-inv-int (a + da) | right-inv-int (b + db) | right-id-int (a + da + (b + db)) = mn·pq=mp·nq {a} {da} {b} {db}
validDeriveConst minus = binary-valid (λ a da ada b db bdb → tt) dminus-eq
  where
    open import Data.Integer
    open import Theorem.Groups-Nehemiah
    open BinaryValid ⟦ minus ⟧Const (changeSemConst minus)
    dminus-eq : binary-valid-eq-hp
    dminus-eq a da ada b db bdb rewrite right-inv-int (a + da) | right-inv-int (b + db) | right-id-int (a + da - (b + db)) | sym (-m·-n=-mn {b} {db}) = mn·pq=mp·nq {a} {da} { - b} { - db}
validDeriveConst linj a da ada = sv₁ a da ada , cong inj₁ (update-nil (a ⊕ da))
validDeriveConst rinj b db bdb = sv₂ b db bdb , cong inj₂ (update-nil (b ⊕ db))

correctDerive (const c) ρ dρ ρdρ rewrite changeSemConst-rewrite c ρ dρ = correctDeriveConst c
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
validDerive (const c) ρ dρ ρdρ rewrite changeSemConst-rewrite c ρ dρ = validDeriveConst c
