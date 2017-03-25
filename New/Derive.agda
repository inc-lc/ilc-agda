module New.Derive where

open import New.Lang
open import New.Changes
open import New.LangChanges
open import New.LangOps

deriveConst : ∀ {τ} →
  Const τ →
  Term ∅ (Δt τ)
-- dplus = λ m dm n dn → (m + dm) + (n + dn) - (m + n) = dm + dn
deriveConst (lit n) = const (lit (+ 0))
deriveConst plus = abs (abs (abs (abs (app₂ (const plus) (var (that (that this))) (var this)))))
-- minus = λ m n → m - n
-- dminus = λ m dm n dn → (m + dm) - (n + dn) - (m - n) = dm - dn
deriveConst minus = abs (abs (abs (abs (app₂ (const minus) (var (that (that this))) (var this)))))
deriveConst cons = abs (abs (abs (abs (app (app (const cons) (var (that (that this)))) (var this)))))
deriveConst fst = abs (abs (app (const fst) (var this)))
deriveConst snd = abs (abs (app (const snd) (var this)))
deriveConst linj = abs (abs (app (const linj) (app (const linj) (var this))))
deriveConst rinj = abs (abs (app (const linj) (app (const rinj) (var this))))
deriveConst (match {t1} {t2} {t3}) =
  -- λ s ds f df g dg →
  abs (abs (abs (abs (abs (abs
    -- match ds
    (app₃ (const match) (var (that (that (that (that this)))))
      -- λ ds₁ → match ds₁
      (abs (app₃ (const match) (var this)
        -- case inj₁ da → absV 1 (λ da → match s
        (abs (app₃ (const match) (var (that (that (that (that (that (that (that this))))))))
          -- λ a → app₂ df a da
          (abs (app₂ (var (that (that (that (that (that this)))))) (var this) (var (that this))))
          -- absurd: λ b → dg b (nil b)
          (abs (app₂ (var (that (that (that this)))) (var this) (app (onilτo t2) (var this))))))
        -- case inj₂ db → absV 1 (λ db → match s
        (abs (app₃ (const match) (var (that (that (that (that (that (that (that this))))))))
          -- absurd: λ a → df a (nil a)
          (abs (app₂ (var (that (that (that (that (that this)))))) (var this) (app (onilτo t1) (var this))))
          -- λ b → app₂ dg b db
          (abs (app₂ (var (that (that (that this)))) (var this) (var (that this))))))))
      -- recomputation branch:
      -- λ s2 → ominus (match s2 (f ⊕ df) (g ⊕ dg)) (match s f g)
      (abs (app₂ (ominusτo t3)
        -- (match s2 (f ⊕ df) (g ⊕ dg))
        (app₃ (const match)
          (var this)
          (app₂ (oplusτo (t1 ⇒ t3))
            (var (that (that (that (that this)))))
            (var (that (that (that this)))))
          (app₂ (oplusτo (t2 ⇒ t3))
            (var (that (that this)))
            (var (that this))))
        -- (match s f g)
        (app₃ (const match)
          (var (that (that (that (that (that (that this)))))))
          (var (that (that (that (that this)))))
          (var (that (that this))))))))))))

{-
derive (λ s f g → match s f g) =
λ s ds f df g dg →
case ds of
 ch1 da →
   case s of
     inj1 a → df a da
     inj2 b → {- absurd -} dg b (nil b)
  ch2 db →
   case s of
     inj2 b → dg b db
     inj1 a → {- absurd -} df a (nil a)
  rp s2 →
    match (f ⊕ df) (g ⊕ dg) s2 ⊝
    match f g s
-}

Γ≼ΔΓ : ∀ {Γ} → Γ ≼ ΔΓ Γ
Γ≼ΔΓ {∅} = ∅
Γ≼ΔΓ {τ • Γ} = drop Δt τ • keep τ • Γ≼ΔΓ

deriveVar : ∀ {Γ τ} → Var Γ τ → Var (ΔΓ Γ) (Δt τ)
deriveVar this = this
deriveVar (that x) = that (that (deriveVar x))

fit : ∀ {τ Γ} → Term Γ τ → Term (ΔΓ Γ) τ
fit = weaken Γ≼ΔΓ

derive : ∀ {Γ τ} → Term Γ τ → Term (ΔΓ Γ) (Δt τ)
derive (const c) = weaken (∅≼Γ {ΔΓ _}) (deriveConst c)
derive (var x) = var (deriveVar x)
derive (app s t) = app (app (derive s) (fit t)) (derive t)
derive (abs t) = abs (abs (derive t))

-- Lemmas needed to reason about derivation, for any correctness proof
-- The change semantics is just the semantics composed with derivation!
⟦_⟧ΔVar : ∀ {Γ τ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) → Chτ τ
⟦ x ⟧ΔVar ρ dρ = ⟦ deriveVar x ⟧Var dρ

⟦_⟧ΔTerm : ∀ {Γ τ} → (t : Term Γ τ) → (ρ : ⟦ Γ ⟧Context) (dρ : eCh Γ) → Chτ τ
⟦ t ⟧ΔTerm ρ dρ = ⟦ derive t ⟧Term dρ

⟦_⟧ΔConst : ∀ {τ} (c : Const τ) → Chτ τ
⟦ c ⟧ΔConst = ⟦ deriveConst c ⟧Term ∅

⟦_⟧ΔConst-rewrite : ∀ {τ Γ} (c : Const τ) (ρ : ⟦ Γ ⟧Context) dρ → ⟦_⟧ΔTerm (const c) ρ dρ ≡ ⟦ c ⟧ΔConst
⟦ c ⟧ΔConst-rewrite ρ dρ rewrite weaken-sound {Γ₁≼Γ₂ = ∅≼Γ} (deriveConst c) dρ | ⟦∅≼Γ⟧-∅ dρ = refl

module _ {t1 t2 t3 : Type}
  (f : ⟦ t1 ⟧Type → ⟦ t3 ⟧Type)
  (df : Chτ (t1 ⇒ t3))
  (g : ⟦ t2 ⟧Type → ⟦ t3 ⟧Type)
  (dg : Chτ (t2 ⇒ t3))
  where
  private
    Γ : Context
    Γ = sum t1 t2 •
      (t2 ⇒ Δt t2 ⇒ Δt t3) •
      (t2 ⇒ t3) •
      (t1 ⇒ Δt t1 ⇒ Δt t3) •
      (t1 ⇒ t3) •
      sum (sum (Δt t1) (Δt t2)) (sum t1 t2) •
      sum t1 t2 • ∅
  module _ where
    private
      Γ′ Γ′′ : Context
      Γ′ = t2 • (t2 ⇒ Δt t2 ⇒ Δt t3) • (t2 ⇒ t3) • Γ
      Γ′′ = t2 • Γ′
    changeMatchSem-lem1 :
      ∀ a1 b2 →
        ⟦ match ⟧ΔConst (inj₁ a1) (inj₂ (inj₂ b2)) f df g dg
      ≡
        g b2 ⊕ dg b2 (nil b2) ⊝ f a1
    changeMatchSem-lem1 a1 b2 rewrite ominusτ-equiv-ext t2 Γ′′ | oplusτ-equiv-ext t3 Γ′ | ominusτ-equiv-ext t3 Γ = refl
  module _ where
    private
      Γ′ Γ′′ : Context
      Γ′ = t1 • (t1 ⇒ Δt t1 ⇒ Δt t3) • (t1 ⇒ t3) • Γ
      Γ′′ = t1 • Γ′
    changeMatchSem-lem2 :
      ∀ b1 a2 →
        ⟦ match ⟧ΔConst (inj₂ b1) (inj₂ (inj₁ a2)) f df g dg
      ≡
        f a2 ⊕ df a2 (nil a2) ⊝ g b1
    changeMatchSem-lem2 b1 a2 rewrite ominusτ-equiv-ext t1 Γ′′ | oplusτ-equiv-ext t3 Γ′ | ominusτ-equiv-ext t3 Γ = refl
