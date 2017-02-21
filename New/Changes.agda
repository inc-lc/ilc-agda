module New.Changes where

open import Data.Product public hiding (map)
open import Data.Sum public hiding (map)
open import Data.Unit.Base public

open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Postulate.Extensionality public
open import Level

open import Theorem.Groups-Nehemiah public

record IsChAlg {ℓ : Level} (A : Set ℓ) (Ch : Set ℓ) : Set (suc ℓ) where
  field
    _⊕_ : A → Ch → A
    _⊝_ : A → A → Ch
    valid : A → Ch → Set ℓ
    _⊚[_]_ : Ch → A → Ch → Ch
    ⊝-valid : ∀ (a b : A) → valid a (b ⊝ a)
    ⊕-⊝ : (b a : A) → a ⊕ (b ⊝ a) ≡ b
    ⊚-correct : ∀ (a : A) → (da1 : Ch) → valid a da1 → (da2 : Ch) → valid (a ⊕ da1) da2 →
      a ⊕ da1 ⊚[ a ] da2 ≡ a ⊕ da1 ⊕ da2
    ⊚-valid : (a : A) → (da1 : Ch) → valid a da1 → (da2 : Ch) → valid (a ⊕ da1) da2 → valid a (da1 ⊚[ a ] da2)
  infixl 6 _⊕_ _⊝_

  Δ : A → Set ℓ
  Δ a = Σ[ da ∈ Ch ] (valid a da)

  update-diff = ⊕-⊝

  nil : A → Ch
  nil a = a ⊝ a
  nil-valid : (a : A) → valid a (nil a)
  nil-valid a = ⊝-valid a a
  update-nil : (a : A) → a ⊕ nil a ≡ a
  update-nil a = update-diff a a

  default-⊚ : Ch → A → Ch → Ch
  default-⊚ da1 a da2 = a ⊕ da1 ⊕ da2 ⊝ a
  default-⊚-valid : (a : A) → (da1 : Ch) → valid a da1 → (da2 : Ch) → valid (a ⊕ da1) da2 → valid a (default-⊚ da1 a da2)
  default-⊚-valid a da1 ada1 da2 ada2 = ⊝-valid a (a ⊕ da1 ⊕ da2)
  default-⊚-correct : ∀ (a : A) → (da1 : Ch) → valid a da1 → (da2 : Ch) → valid (a ⊕ da1) da2 →
      a ⊕ default-⊚ da1 a da2 ≡ a ⊕ da1 ⊕ da2
  default-⊚-correct a da1 ada1 da2 ada2 = update-diff (a ⊕ da1 ⊕ da2) a

record ChAlg {ℓ : Level} (A : Set ℓ) : Set (suc ℓ) where
  field
    Ch : Set ℓ
    isChAlg : IsChAlg A Ch
  open IsChAlg isChAlg public

open ChAlg {{...}} public hiding (Ch)
Ch : ∀ {ℓ} (A : Set ℓ) → {{CA : ChAlg A}} → Set ℓ
Ch A {{CA}} = ChAlg.Ch CA

-- Huge hack, but it does gives the output you want to see in all cases I've seen.

{-# DISPLAY IsChAlg.valid x = valid #-}
{-# DISPLAY ChAlg.valid x = valid #-}
{-# DISPLAY IsChAlg._⊕_ x = _⊕_ #-}
{-# DISPLAY ChAlg._⊕_ x = _⊕_ #-}
{-# DISPLAY IsChAlg.nil x = nil #-}
{-# DISPLAY ChAlg.nil x = nil #-}
{-# DISPLAY IsChAlg._⊝_ x = _⊝_ #-}
{-# DISPLAY ChAlg._⊝_ x = _⊝_ #-}

module _ {ℓ₁} {ℓ₂}
  {A : Set ℓ₁} {B : Set ℓ₂} {{CA : ChAlg A}} {{CB : ChAlg B}} where
  open ≡-Reasoning
  open import Postulate.Extensionality
  instance
    funCA : ChAlg (A → B)
  private
    fCh = A → Ch A → Ch B
    _f⊕_ : (A → B) → fCh → A → B
    _f⊕_ = λ f df a → f a ⊕ df a (nil a)
    _f⊝_ : (g f : A → B) → fCh
    _f⊝_ = λ g f a da → g (a ⊕ da) ⊝ f a

  IsDerivative : ∀ (f : A → B) → (df : fCh) → Set (ℓ₁ ⊔ ℓ₂)
  IsDerivative f df = ∀ a da (v : valid a da) → f (a ⊕ da) ≡ f a ⊕ df a da

  WellDefinedFunChangePoint : ∀ (f : A → B) → (df : fCh) → ∀ a da (v : valid a da) → Set ℓ₂
  WellDefinedFunChangePoint f df a da ada = (f f⊕ df) (a ⊕ da) ≡ f a ⊕ df a da

  WellDefinedFunChange : ∀ (f : A → B) → (df : fCh) → Set (ℓ₁ ⊔ ℓ₂)
  WellDefinedFunChange f df = ∀ a da ada → WellDefinedFunChangePoint f df a da ada

  private
    fvalid : (A → B) → fCh → Set (ℓ₁ ⊔ ℓ₂)
    fvalid =  λ f df → ∀ a da (ada : valid a da) →
        valid (f a) (df a da) ×
        WellDefinedFunChangePoint f df a da ada
    f⊝-valid : ∀ (f g : A → B) → fvalid f (g f⊝ f)
    f⊝-valid = λ f g a da (v : valid a da) →
         ⊝-valid (f a) (g (a ⊕ da))
        , ( begin
          f (a ⊕ da) ⊕ (g (a ⊕ da ⊕ nil (a ⊕ da)) ⊝ f (a ⊕ da))
        ≡⟨ cong (λ □ → f (a ⊕ da) ⊕ (g □ ⊝ f (a ⊕ da)))
             (update-nil (a ⊕ da)) ⟩
          f (a ⊕ da) ⊕ (g (a ⊕ da) ⊝ f (a ⊕ da))
        ≡⟨ update-diff (g (a ⊕ da)) (f (a ⊕ da)) ⟩
          g (a ⊕ da)
        ≡⟨ sym (update-diff (g (a ⊕ da)) (f a)) ⟩
          f a ⊕ (g (a ⊕ da) ⊝ f a)
        ∎)

    -- Two alternatives. Proofs on f⊚ are a bit easier.
    -- f⊚ is optimized relying on the incrementalization property for df2.
    f⊚ f⊚2 : fCh → (A → B) → fCh → fCh
    f⊚ df1 f df2 = λ a da → (df1 a (nil a)) ⊚[ f a ] (df2 a da)
    f⊚-valid : (f : A → B) → (df1 : fCh) → fvalid f df1 → (df2 : fCh) → fvalid (f f⊕ df1) df2 → fvalid f (f⊚ df1 f df2)
    f⊚-valid f df1 fdf1 df2 fdf2 a da ada
      rewrite ⊚-correct (f a) (df1 a (nil a)) (proj₁ (fdf1 a (nil a) (nil-valid a))) (df2 a da) (proj₁ (fdf2 a da ada))
      | ⊚-correct
        (f (a ⊕ da))
        (df1 (a ⊕ da) (nil (a ⊕ da))) (proj₁ (fdf1 (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da))))
        (df2 (a ⊕ da) (nil (a ⊕ da))) (proj₁ (fdf2 (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da))))
      =
        ⊚-valid (f a) (df1 a (nil a)) (proj₁ (fdf1 a (nil a) (nil-valid a))) (df2 a da) (proj₁ (fdf2 a da ada))
      , proj₂ (fdf2 a da ada)

    -- f⊚2 is optimized relying on the incrementalization property for df1, so we need to use that property to rewrite some goals.
    f⊚2 df1 f df2 = λ a da → df1 a da ⊚[ f a ] df2 (a ⊕ da) (nil (a ⊕ da))
    f⊚-valid2 : (f : A → B) → (df1 : fCh) → fvalid f df1 → (df2 : fCh) → fvalid (f f⊕ df1) df2 → fvalid f (f⊚2 df1 f df2)
    f⊚-valid2 f df1 fdf1 df2 fdf2 = lemma
      where
        -- Prove that (df2 (a ⊕ da) (nil (a ⊕ da))) is valid for (f a ⊕ df1 a da).
        -- Using the incrementalization property for df1, that becomes (f ⊕ df1) (a ⊕ da).
        --
        -- Since df2 is valid for f ⊕ df1, it follows that (df2 (a ⊕ da) (nil (a ⊕ da)))
        -- is indeed valid for (f ⊕ df1) (a ⊕ da).
        valid-df2-a2-nila2 : ∀ a da → (valid a da) → valid (f a ⊕ df1 a da) (df2 (a ⊕ da) (nil (a ⊕ da)))
        valid-df2-a2-nila2 a da ada rewrite sym (proj₂ (fdf1 a da ada)) = proj₁ (fdf2 (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da)))

        lemma : fvalid f (f⊚2 df1 f df2)
        lemma a da ada
          rewrite ⊚-correct
            (f a)
            (df1 a da) (proj₁ (fdf1 a da ada))
            (df2 (a ⊕ da) (nil (a ⊕ da))) (valid-df2-a2-nila2 a da ada)
          | update-nil (a ⊕ da)
          | ⊚-correct
            (f (a ⊕ da))
            (df1 (a ⊕ da) (nil (a ⊕ da))) (proj₁ (fdf1 (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da))))
            (df2 (a ⊕ da) (nil (a ⊕ da))) (proj₁ (fdf2 (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da))))
          | proj₂ (fdf1 a da ada)
          = ⊚-valid (f a) (df1 a da) (proj₁ (fdf1 a da ada)) (df2 (a ⊕ da) (nil (a ⊕ da))) (valid-df2-a2-nila2 a da ada)
          , refl

    f⊚-correct : ∀ (f : A → B) → (df1 : fCh) → fvalid f df1 → (df2 : fCh) → fvalid (f f⊕ df1) df2 → (a : A) →
      (f f⊕ f⊚ df1 f df2) a ≡ ((f f⊕ df1) f⊕ df2) a
    f⊚-correct f df1 fdf1 df2 fdf2 a = ⊚-correct (f a) (df1 a (nil a)) (proj₁ (fdf1 a (nil a) (nil-valid a))) (df2 a (nil a)) (proj₁ (fdf2 a (nil a) (nil-valid a)))

  private
    funUpdateDiff : ∀ g f a → (f f⊕ (g f⊝ f)) a ≡ g a
  funUpdateDiff g f a rewrite update-nil a = update-diff (g a) (f a)
  funCA = record
    { Ch = A → Ch A → Ch B
    ; isChAlg = record
      { _⊕_ = _f⊕_
      ; _⊝_ = _f⊝_
      ; valid = fvalid
      ; _⊚[_]_ = f⊚
      ; ⊝-valid = f⊝-valid
      ; ⊕-⊝ = λ g f → ext (funUpdateDiff g f)
      ; ⊚-correct = λ f df1 fdf1 df2 fdf2 → ext (f⊚-correct f df1 fdf1 df2 fdf2)
      ; ⊚-valid = f⊚-valid
      } }

  private
    pCh = Ch A × Ch B
    _p⊕_ : A × B → Ch A × Ch B → A × B
    _p⊕_ (a , b) (da , db) = a ⊕ da , b ⊕ db
    _p⊝_ : A × B → A × B → pCh
    _p⊝_ (a2 , b2) (a1 , b1) = a2 ⊝ a1 , b2 ⊝ b1
    pvalid : A × B → pCh → Set (ℓ₂ ⊔ ℓ₁)
    pvalid (a , b) (da , db) = valid a da × valid b db
    p⊝-valid : (p1 p2 : A × B) → pvalid p1 (p2 p⊝ p1)
    p⊝-valid (a1 , b1) (a2 , b2) = ⊝-valid a1 a2 , ⊝-valid b1 b2
    p⊕-⊝ : (p2 p1 : A × B) → p1 p⊕ (p2 p⊝ p1) ≡ p2
    p⊕-⊝ (a2 , b2) (a1 , b1) = cong₂ _,_ (⊕-⊝ a2 a1) (⊕-⊝ b2 b1)
    _p⊚[_]_ : pCh → A × B → pCh → pCh
    (da1 , db1) p⊚[ a , b ] (da2 , db2) = da1 ⊚[ a ] da2 , db1 ⊚[ b ] db2
    p⊚-valid : (p : A × B) (dp1 : pCh) →
      pvalid p dp1 →
      (dp2 : pCh) → pvalid (p p⊕ dp1) dp2 → pvalid p (dp1 p⊚[ p ] dp2)
    p⊚-valid (a , b) (da1 , db1) (ada1 , bdb1) (da2 , db2) (ada2 , bdb2) = ⊚-valid a da1 ada1 da2 ada2 , ⊚-valid b db1 bdb1 db2 bdb2
    p⊚-correct : (p : A × B) (dp1 : pCh) →
      pvalid p dp1 →
      (dp2 : pCh) → pvalid (p p⊕ dp1) dp2 → p p⊕ (dp1 p⊚[ p ] dp2) ≡ (p p⊕ dp1) p⊕ dp2
    p⊚-correct (a , b) (da1 , db1) (ada1 , bdb1) (da2 , db2) (ada2 , bdb2) rewrite ⊚-correct a da1 ada1 da2 ada2 | ⊚-correct b db1 bdb1 db2 bdb2 = refl
  instance
    pairCA : ChAlg (A × B)
  pairCA = record
    { Ch = pCh
    ; isChAlg = record
    { _⊕_ = _p⊕_
    ; _⊝_ = _p⊝_
    ; valid = pvalid
    ; ⊝-valid = p⊝-valid
    ; ⊕-⊝ = p⊕-⊝
    ; _⊚[_]_ = _p⊚[_]_
    ; ⊚-valid = p⊚-valid
    ; ⊚-correct = p⊚-correct
    } }

  private
    SumChange = (Ch A ⊎ Ch B) ⊎ (A ⊎ B)

  data SumChange2 : Set (ℓ₁ ⊔ ℓ₂) where
    ch₁ : (da : Ch A) → SumChange2
    ch₂ : (db : Ch B) → SumChange2
    rp : (s : A ⊎ B) → SumChange2

  convert : SumChange → SumChange2
  convert (inj₁ (inj₁ da)) = ch₁ da
  convert (inj₁ (inj₂ db)) = ch₂ db
  convert (inj₂ s) = rp s
  convert₁ : SumChange2 → SumChange
  convert₁ (ch₁ da) = inj₁ (inj₁ da)
  convert₁ (ch₂ db) = inj₁ (inj₂ db)
  convert₁ (rp s) = inj₂ s

  data SValid : A ⊎ B → SumChange → Set (ℓ₁ ⊔ ℓ₂) where
    sv₁ : ∀ (a : A) (da : Ch A) (ada : valid a da) → SValid (inj₁ a) (convert₁ (ch₁ da))
    sv₂ : ∀ (b : B) (db : Ch B) (bdb : valid b db) → SValid (inj₂ b) (convert₁ (ch₂ db))
    svrp₁ : ∀ a1 b2 → SValid (inj₁ a1) (convert₁ (rp (inj₂ b2)))
    svrp₂ : ∀ b1 a2 → SValid (inj₂ b1) (convert₁ (rp (inj₁ a2)))

  inv1 : ∀ ds → convert₁ (convert ds) ≡ ds
  inv1 (inj₁ (inj₁ da)) = refl
  inv1 (inj₁ (inj₂ db)) = refl
  inv1 (inj₂ s) = refl
  inv2 : ∀ ds → convert (convert₁ ds) ≡ ds
  inv2 (ch₁ da) = refl
  inv2 (ch₂ db) = refl
  inv2 (rp s) = refl

  private
    s⊕2 : A ⊎ B → SumChange2 → A ⊎ B
    s⊕2 (inj₁ a) (ch₁ da) = inj₁ (a ⊕ da)
    s⊕2 (inj₂ b) (ch₂ db) = inj₂ (b ⊕ db)
    s⊕2 (inj₂ b) (ch₁ da) = inj₂ b -- invalid
    s⊕2 (inj₁ a) (ch₂ db) = inj₁ a -- invalid
    s⊕2 s (rp s₁) = s₁

    s⊕ : A ⊎ B → SumChange → A ⊎ B
    s⊕ s ds = s⊕2 s (convert ds)

    s⊝2 : A ⊎ B → A ⊎ B → SumChange2
    s⊝2 (inj₁ x2) (inj₁ x1) = ch₁ (x2 ⊝ x1)
    s⊝2 (inj₂ y2) (inj₂ y1) = ch₂ (y2 ⊝ y1)
    s⊝2 s2 s1 = rp s2

    s⊝ : A ⊎ B → A ⊎ B → SumChange
    s⊝ s2 s1 = convert₁ (s⊝2 s2 s1)

    s⊝-valid : (a b : A ⊎ B) → SValid a (s⊝ b a)
    s⊝-valid (inj₁ x1) (inj₁ x2) = sv₁ x1 (x2 ⊝ x1) (⊝-valid x1 x2)
    s⊝-valid (inj₂ y1) (inj₂ y2) = sv₂ y1 (y2 ⊝ y1) (⊝-valid y1 y2)
    s⊝-valid s1@(inj₁ x) s2@(inj₂ y) = svrp₁ x y
    s⊝-valid s1@(inj₂ y) s2@(inj₁ x) = svrp₂ y x

    s⊕-⊝ : (b a : A ⊎ B) → s⊕ a (s⊝ b a) ≡ b
    s⊕-⊝ (inj₁ x2) (inj₁ x1) rewrite ⊕-⊝ x2 x1 = refl
    s⊕-⊝ (inj₁ x2) (inj₂ y1) = refl
    s⊕-⊝ (inj₂ y2) (inj₁ x1) = refl
    s⊕-⊝ (inj₂ y2) (inj₂ y1) rewrite ⊕-⊝ y2 y1 = refl
    {-# TERMINATING #-}
    isSumCA : IsChAlg (A ⊎ B) SumChange
    s⊚-valid : (a : A ⊎ B) (da1 : SumChange) →
      SValid a da1 →
      (da2 : SumChange) →
      SValid (s⊕ a da1) da2 →
      SValid a (IsChAlg.default-⊚ isSumCA da1 a da2)
    s⊚-correct : (a : A ⊎ B) (da1 : SumChange) →
      SValid a da1 →
      (da2 : SumChange) →
      SValid (s⊕ a da1) da2 →
      s⊕ a (IsChAlg.default-⊚ isSumCA da1 a da2) ≡
      s⊕ (s⊕ a da1) da2

  sumCA : ChAlg (A ⊎ B)
  isSumCA = record
    { _⊕_ = s⊕
    ; _⊝_ = s⊝
    ; valid = SValid
    ; ⊝-valid = s⊝-valid
    ; ⊕-⊝ = s⊕-⊝
    ; _⊚[_]_ = IsChAlg.default-⊚ isSumCA
    ; ⊚-valid = s⊚-valid
    ; ⊚-correct = s⊚-correct
    }

  s⊚-valid = IsChAlg.default-⊚-valid isSumCA
  s⊚-correct = IsChAlg.default-⊚-correct isSumCA

  sumCA = record
    { Ch = SumChange
    ; isChAlg = isSumCA }

open import Data.Integer

instance
  intCA : ChAlg ℤ
intCA = record
  { Ch = ℤ
  ; isChAlg = record
  { _⊕_ = _+_
  ; _⊝_ = _-_
  ; valid = λ a b → ⊤
  ; ⊝-valid = λ a b → tt
  ; ⊕-⊝ = λ b a → n+[m-n]=m {a} {b}
  ; ⊚-valid = λ a da1 _ da2 _ → tt
  ; ⊚-correct = λ a da1 _ da2 _ → sym (associative-int a da1 da2)
  } }
