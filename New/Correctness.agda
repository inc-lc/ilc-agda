module New.Correctness where

open import Function hiding (const)
open import New.Lang
open import New.Changes
open import New.Derive
open import New.LangChanges
open import New.LangOps
open import New.FunctionLemmas
open import New.Unused

⟦Γ≼ΔΓ⟧ : ∀ {Γ} (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → validΓ ρ dρ →
  ρ ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ ∅ ∅ tt = refl
⟦Γ≼ΔΓ⟧ (v • ρ) (dv • .v • dρ) (vdv , refl , ρdρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ ρ dρ ρdρ)

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → validΓ ρ dρ →
  ⟦ t ⟧Term ρ ≡ ⟦ fit t ⟧Term dρ
fit-sound t ρ dρ ρdρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ ρ dρ ρdρ))
  (sym (weaken-sound t _))

correctDeriveConst : ∀ {τ} (c : Const τ) → ⟦ c ⟧Const ≡ ⟦ c ⟧Const ⊕ (⟦_⟧ΔConst c)
correctDeriveConst (lit n) = sym (right-id-int n)
correctDeriveConst plus = ext (λ m → ext (lemma m))
  where
    lemma : ∀ m n → m + n ≡ m + n + (m + - m + (n + - n))
    lemma m n rewrite right-inv-int m | right-inv-int n | right-id-int (m + n) = refl

correctDeriveConst minus = ext (λ m → ext (λ n → lemma m n))
  where
    lemma : ∀ m n → m - n ≡ m - n + (m + - m - (n + - n))
    lemma m n rewrite right-inv-int m | right-inv-int n | right-id-int (m - n) = refl
correctDeriveConst cons = ext (λ v1 → ext (λ v2 → sym (update-nil (v1 , v2))))
correctDeriveConst fst = ext (λ vp → sym (update-nil (proj₁ vp)))
correctDeriveConst snd = ext (λ vp → sym (update-nil (proj₂ vp)))
correctDeriveConst linj = ext (λ va → sym (cong inj₁ (update-nil va)))
correctDeriveConst rinj = ext (λ vb → sym (cong inj₂ (update-nil vb)))
correctDeriveConst (match {t1} {t2} {t3}) = ext³ lemma
  where
    lemma : ∀ s f g →
      ⟦ match {t1} {t2} {t3} ⟧Const s f g ≡
      (⟦ match ⟧Const ⊕ ⟦ match ⟧ΔConst) s f g
    lemma (inj₁ x) f g rewrite update-nil x | update-nil (f x) = refl
    lemma (inj₂ y) f g rewrite update-nil y | update-nil (g y) = refl

validDeriveConst : ∀ {τ} (c : Const τ) → valid ⟦ c ⟧Const (⟦_⟧ΔConst c)
validDeriveConst (lit n) = tt
validDeriveConst {τ = t1 ⇒ t2 ⇒ pair .t1 .t2} cons = binary-valid (λ a da ada b db bdb → (ada , bdb)) dcons-eq
  where
    open BinaryValid ⟦ cons {t1} {t2} ⟧Const (⟦ cons ⟧ΔConst)
    dcons-eq : binary-valid-eq-hp
    dcons-eq a da ada b db bdb rewrite update-nil (a ⊕ da) | update-nil (b ⊕ db) = refl
validDeriveConst fst (a , b) (da , db) (ada , bdb) = ada , update-nil (a ⊕ da)
validDeriveConst snd (a , b) (da , db) (ada , bdb) = bdb , update-nil (b ⊕ db)

validDeriveConst plus = binary-valid (λ a da ada b db bdb → tt) dplus-eq
  where
    open BinaryValid ⟦ plus ⟧Const (⟦ plus ⟧ΔConst)
    dplus-eq : binary-valid-eq-hp
    dplus-eq a da ada b db bdb rewrite right-inv-int (a + da) | right-inv-int (b + db) | right-id-int (a + da + (b + db)) = mn·pq=mp·nq {a} {da} {b} {db}
validDeriveConst minus = binary-valid (λ a da ada b db bdb → tt) dminus-eq
  where
    open BinaryValid ⟦ minus ⟧Const (⟦ minus ⟧ΔConst)
    dminus-eq : binary-valid-eq-hp
    dminus-eq a da ada b db bdb rewrite right-inv-int (a + da) | right-inv-int (b + db) | right-id-int (a + da - (b + db)) | sym (-m·-n=-mn {b} {db}) = mn·pq=mp·nq {a} {da} { - b} { - db}
validDeriveConst linj a da ada = sv₁ a da ada , cong inj₁ (update-nil (a ⊕ da))
validDeriveConst rinj b db bdb = sv₂ b db bdb , cong inj₂ (update-nil (b ⊕ db))
validDeriveConst (match {t1} {t2} {t3}) =
  ternary-valid dmatch-valid dmatch-eq
  where
    open TernaryValid {{chAlgt (sum t1 t2)}} {{chAlgt (t1 ⇒ t3)}} {{chAlgt (t2 ⇒ t3)}} {{chAlgt t3}} ⟦ match ⟧Const (⟦ match ⟧ΔConst)

    dmatch-valid : ternary-valid-preserve-hp
    dmatch-valid .(inj₁ a) .(inj₁ (inj₁ da)) (sv₁ a da ada) f df fdf g dg gdg = proj₁ (fdf a da ada)
    dmatch-valid .(inj₂ b) .(inj₁ (inj₂ db)) (sv₂ b db bdb) f df fdf g dg gdg = proj₁ (gdg b db bdb)
    dmatch-valid .(inj₁ a1) .(inj₂ (inj₂ b2)) (svrp₁ a1 b2) f df fdf g dg gdg
      rewrite changeMatchSem-lem1 f df g dg a1 b2
      = ⊝-valid (f a1) (g b2 ⊕ dg b2 (nil b2))
    dmatch-valid .(inj₂ b1) .(inj₂ (inj₁ a2)) (svrp₂ b1 a2) f df fdf g dg gdg
      rewrite changeMatchSem-lem2 f df g dg b1 a2
      = ⊝-valid (g b1) (f a2 ⊕ df a2 (nil a2))
    dmatch-eq : ternary-valid-eq-hp
    dmatch-eq .(inj₁ a) .(inj₁ (inj₁ da)) (sv₁ a da ada) f df fdf g dg gdg
      rewrite update-nil (a ⊕ da)
      | update-nil (f (a ⊕ da) ⊕ df (a ⊕ da) (nil (a ⊕ da))) = proj₂ (fdf a da ada)
    dmatch-eq .(inj₂ b) .(inj₁ (inj₂ db)) (sv₂ b db bdb) f df fdf g dg gdg
      rewrite update-nil (b ⊕ db)
      | update-nil (g (b ⊕ db) ⊕ dg (b ⊕ db) (nil (b ⊕ db))) = proj₂ (gdg b db bdb)
    dmatch-eq .(inj₁ a1) .(inj₂ (inj₂ b2)) (svrp₁ a1 b2) f df fdf g dg gdg
      rewrite changeMatchSem-lem1 f df g dg a1 b2
      | update-nil b2
      | update-diff (g b2 ⊕ dg b2 (nil b2)) (f a1)
      | update-nil (g b2 ⊕ dg b2 (nil b2))
      = refl
    dmatch-eq .(inj₂ b1) .(inj₂ (inj₁ a2)) (svrp₂ b1 a2) f df fdf g dg gdg
      rewrite changeMatchSem-lem2 f df g dg b1 a2
      | update-nil a2
      | update-diff (f a2 ⊕ df a2 (nil a2)) (g b1)
      | update-nil (f a2 ⊕ df a2 (nil a2))
      = refl

validDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) →
  validΓ ρ dρ → valid (⟦ x ⟧Var ρ) (⟦ x ⟧ΔVar ρ dρ)

validDeriveVar this (v • ρ) (dv • .v • dρ) (vdv , refl , ρdρ) = vdv
validDeriveVar (that x) (v • ρ) (dv • .v • dρ) (vdv , refl , ρdρ) = validDeriveVar x ρ dρ ρdρ

correctDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  IsDerivative ⟦ x ⟧Var (⟦ x ⟧ΔVar)
correctDeriveVar this (v • ρ) (dv • v' • dρ) ρdρ = refl
correctDeriveVar (that x) (v • ρ) (dv • .v • dρ) (vdv , refl , ρdρ) = correctDeriveVar x ρ dρ ρdρ

validDerive : ∀ {Γ τ} → (t : Term Γ τ) →
  (ρ : ⟦ Γ ⟧Context) (dρ : ChΓ Γ) → validΓ ρ dρ →
    valid (⟦ t ⟧Term ρ) (⟦ t ⟧ΔTerm ρ dρ)
correctDerive : ∀ {Γ τ} → (t : Term Γ τ) →
  IsDerivative ⟦ t ⟧Term ⟦ t ⟧ΔTerm

correctDerive (const c) ρ dρ ρdρ rewrite ⟦ c ⟧ΔConst-rewrite ρ dρ = correctDeriveConst c
correctDerive (var x) ρ dρ ρdρ = correctDeriveVar x ρ dρ ρdρ
correctDerive (app s t) ρ dρ ρdρ rewrite sym (fit-sound t ρ dρ ρdρ) =
  let
    open ≡-Reasoning
    a0 = ⟦ t ⟧Term ρ
    da0 = ⟦ derive t ⟧Term dρ
    a0da0 = validDerive t ρ dρ ρdρ
  in
    begin
      ⟦ s ⟧Term (ρ ⊕ dρ) (⟦ t ⟧Term (ρ ⊕ dρ))
    ≡⟨ correctDerive s ρ dρ ρdρ ⟨$⟩ correctDerive t ρ dρ ρdρ ⟩
      (⟦ s ⟧Term ρ ⊕ ⟦ s ⟧ΔTerm ρ dρ) (⟦ t ⟧Term ρ ⊕ ⟦ t ⟧ΔTerm ρ dρ)
    ≡⟨ proj₂ (validDerive s ρ dρ ρdρ a0 da0 a0da0)  ⟩
      ⟦ s ⟧Term ρ (⟦ t ⟧Term ρ) ⊕ (⟦ s ⟧ΔTerm ρ dρ) (⟦ t ⟧Term ρ) (⟦ t ⟧ΔTerm ρ dρ)
    ∎
  where
    open import Theorem.CongApp
correctDerive (abs t) ρ dρ ρdρ = ext $ λ a →
  let
    open ≡-Reasoning
    ρ1 = a • ρ
    dρ1 = nil a • a • dρ
    ρ1dρ1 = nil-valid a , refl , ρdρ
  in
    -- equal-future-expand-derivative ⟦ t ⟧Term ⟦ t ⟧ΔTerm (correctDerive t)
    --   ρ1 dρ1 ρ1dρ1
    --   (a • (ρ ⊕ dρ))
    --   (cong (_• ρ ⊕ dρ) (sym (update-nil a)))
    begin
      ⟦ t ⟧Term (a • ρ ⊕ dρ)
    ≡⟨ cong (λ a′ → ⟦ t ⟧Term (a′ • ρ ⊕ dρ)) (sym (update-nil a)) ⟩
      ⟦ t ⟧Term (ρ1 ⊕ dρ1)
    ≡⟨ correctDerive t ρ1 dρ1 ρ1dρ1 ⟩
      ⟦ t ⟧Term ρ1 ⊕ ⟦ t ⟧ΔTerm ρ1 dρ1
    ∎

validDerive (app s t) ρ dρ ρdρ =
  let
    f = ⟦ s ⟧Term ρ
    df = ⟦ derive s ⟧Term dρ
    v = ⟦ t ⟧Term ρ
    dv = ⟦ derive t ⟧Term dρ
    vdv = validDerive t ρ dρ ρdρ
    fdf = validDerive s ρ dρ ρdρ
    fvdfv = proj₁ (fdf v dv vdv)
  in subst (λ v′ → valid (f v) (df v′ dv)) (fit-sound t ρ dρ ρdρ) fvdfv
validDerive (abs t) ρ dρ ρdρ =
  λ a da ada →
  let
    ρ1 = a ⊕ da • ρ
    dρ1 = nil (a ⊕ da) • (a ⊕ da) • dρ
    ρ2 = a • ρ
    dρ2 = da • a • dρ
    ρ1dρ1 = nil-valid (a ⊕ da) , refl , ρdρ
    ρ2dρ2 = ada , refl , ρdρ
    rdr = validDerive t ρ2 dρ2 ρ2dρ2
    open ≡-Reasoning
   in
     rdr ,
     equal-future-derivative ⟦ t ⟧Term ⟦ t ⟧ΔTerm (correctDerive t)
       ρ1 dρ1 ρ1dρ1
       ρ2 dρ2 ρ2dρ2
       (cong (λ a′ → (a′ • ρ ⊕ dρ)) (update-nil (a ⊕ da)))
validDerive (var x) ρ dρ ρdρ = validDeriveVar x ρ dρ ρdρ
validDerive (const c) ρ dρ ρdρ rewrite ⟦ c ⟧ΔConst-rewrite ρ dρ = validDeriveConst c
