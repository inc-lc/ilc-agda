module Thesis.Changes where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality

record IsChangeStructure (A : Set) (ChA : Set) (ch_from_to_ : (dv : ChA) → (v1 v2 : A) → Set) : Set₁ where
  infixl 6 _⊕_ _⊝_
  field
    _⊕_ : A → ChA → A
    fromto→⊕ : ∀ dv v1 v2 →
      ch dv from v1 to v2 →
      v1 ⊕ dv ≡ v2
    _⊝_ : A → A → ChA
    ⊝-fromto : ∀ (a b : A) → ch (b ⊝ a) from a to b

  update-diff : (b a : A) → a ⊕ (b ⊝ a) ≡ b
  update-diff b a = fromto→⊕ (b ⊝ a) a b (⊝-fromto a b)
  nil : A → ChA
  nil a = a ⊝ a
  nil-fromto : (a : A) → ch (nil a) from a to a
  nil-fromto a = ⊝-fromto a a
  update-nil : (a : A) → a ⊕ nil a ≡ a
  update-nil a = update-diff a a

  valid : ∀ (a : A) (da : ChA) → Set
  valid a da = ch da from a to (a ⊕ da)
  Δ₁ : (a : A) → Set
  Δ₁ a = Σ[ da ∈ ChA ] valid a da
  Δ₂ : (a1 : A) (a2 : A) → Set
  Δ₂ a1 a2 = Σ[ da ∈ ChA ] ch da from a1 to a2

  _⊕'_ : (a1 : A) -> {a2 : A} -> (da : Δ₂ a1 a2) -> A
  a1 ⊕' (da , daa) = a1 ⊕ da

record IsCompChangeStructure (A : Set) (ChA : Set) (ch_from_to_ : (dv : ChA) → (v1 v2 : A) → Set) : Set₁ where
  field
    isChangeStructure : IsChangeStructure A ChA ch_from_to_
    _⊚_ : ChA → ChA → ChA
    ⊚-fromto : ∀ (a1 a2 a3 : A) (da1 da2 : ChA) →
      ch da1 from a1 to a2 → ch da2 from a2 to a3 → ch da1 ⊚ da2 from a1 to a3

  open IsChangeStructure isChangeStructure public
  ⊚-correct : ∀ (a1 a2 a3 : A) (da1 da2 : ChA) →
    ch da1 from a1 to a2 → ch da2 from a2 to a3 →
    a1 ⊕ (da1 ⊚ da2) ≡ a3
  ⊚-correct a1 a2 a3 da1 da2 daa1 daa2 = fromto→⊕ _ _ _ (⊚-fromto _ _ _ da1 da2 daa1 daa2)

record ChangeStructure (A : Set) : Set₁ where
  field
    Ch : Set
    ch_from_to_ : (dv : Ch) → (v1 v2 : A) → Set
    isCompChangeStructure : IsCompChangeStructure A Ch ch_from_to_
  open IsCompChangeStructure isCompChangeStructure public

open ChangeStructure {{...}} public hiding (Ch)
Ch : ∀ (A : Set) → {{CA : ChangeStructure A}} → Set
Ch A {{CA}} = ChangeStructure.Ch CA

-- infix 2 Σ-syntax

-- Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
-- Σ-syntax = Σ

-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

⊚-syntax : ∀ (A : Set) → {{CA : ChangeStructure A}} → Ch A → Ch A → Ch A
⊚-syntax A {{CA}} da1 da2 = _⊚_ {{CA}} da1 da2
syntax ⊚-syntax A da1 da2 = da1 ⊚[ A ] da2

{-# DISPLAY IsChangeStructure._⊕_ x = _⊕_ #-}
{-# DISPLAY ChangeStructure._⊕_ x = _⊕_ #-}
{-# DISPLAY IsChangeStructure._⊝_ x = _⊝_ #-}
{-# DISPLAY ChangeStructure._⊝_ x = _⊝_ #-}
{-# DISPLAY IsChangeStructure.nil x = nil #-}
{-# DISPLAY ChangeStructure.nil x = nil #-}
{-# DISPLAY IsCompChangeStructure._⊚_ x = _⊚_ #-}
{-# DISPLAY ChangeStructure._⊚_ x = _⊚_ #-}
{-# DISPLAY ChangeStructure.ch_from_to_ x = ch_from_to_ #-}

module _ {A B : Set} {{CA : ChangeStructure A}} {{CB : ChangeStructure B}} where

  -- In this module, given change structures CA and CB for A and B, we define
  -- change structures for A → B, A × B and A ⊎ B.

  open import Postulate.Extensionality

  -- Functions
  instance
    funCS : ChangeStructure (A → B)

  infixl 6 _f⊕_ _f⊝_
  private
    fCh = A → Ch A → Ch B

    fCh_from_to_ : (df : fCh) → (f1 f2 : A → B) → Set
    fCh_from_to_ =
      λ df f1 f2 → ∀ da (a1 a2 : A) (daa : ch da from a1 to a2) →
        ch df a1 da from f1 a1 to f2 a2

    _f⊕_ : (A → B) → fCh → A → B
    _f⊕_ = λ f df a → f a ⊕ df a (nil a)

    _f⊝_ : (g f : A → B) → fCh
    _f⊝_ = λ g f a da → g (a ⊕ da) ⊝ f a

    f⊝-fromto : ∀ (f1 f2 : A → B) → fCh (f2 f⊝ f1) from f1 to f2
    f⊝-fromto f1 f2 da a1 a2 daa
      rewrite sym (fromto→⊕ da a1 a2 daa) = ⊝-fromto (f1 a1) (f2 (a1 ⊕ da))

    _f⊚_ : fCh → fCh → fCh
    _f⊚_ df1 df2 = λ a da → df1 a (nil a) ⊚[ B ] df2 a da

    _f2⊚_ : fCh → fCh → fCh
    _f2⊚_ df1 df2 = λ a da → df1 a da ⊚[ B ] df2 (a ⊕ da) (nil (a ⊕ da))

    f⊚-fromto : ∀ (f1 f2 f3 : A → B) (df1 df2 : fCh) → fCh df1 from f1 to f2 → fCh df2 from f2 to f3 →
      fCh df1 f⊚ df2 from f1 to f3
    f⊚-fromto f1 f2 f3 df1 df2 dff1 dff2 da a1 a2 daa =
      ⊚-fromto (f1 a1) (f2 a1) (f3 a2)
        (df1 a1 (nil a1))
        (df2 a1 da)
        (dff1 (nil a1) a1 a1 (nil-fromto a1))
        (dff2 da a1 a2 daa)

    f⊚2-fromto : ∀ (f1 f2 f3 : A → B) (df1 df2 : fCh) → fCh df1 from f1 to f2 → fCh df2 from f2 to f3 →
      fCh df1 f2⊚ df2 from f1 to f3
    f⊚2-fromto f1 f2 f3 df1 df2 dff1 dff2 da a1 a2 daa rewrite fromto→⊕ da a1 a2 daa =
      ⊚-fromto (f1 a1) (f2 a2) (f3 a2)
        (df1 a1 da)
        (df2 a2 (nil a2))
        (dff1 da a1 a2 daa)
        (dff2 (nil a2) a2 a2 (nil-fromto a2))

  funCS = record
    { Ch = fCh
    ; ch_from_to_ =
      λ df f1 f2 → ∀ da (a1 a2 : A) (daa : ch da from a1 to a2) →
        ch df a1 da from f1 a1 to f2 a2
    ; isCompChangeStructure = record
      { isChangeStructure = record
        { _⊕_ = _f⊕_
        ; fromto→⊕ = λ df f1 f2 dff →
          ext (λ v →
            fromto→⊕ (df v (nil v)) (f1 v) (f2 v) (dff (nil v) v v (nil-fromto v)))
        ; _⊝_ = _f⊝_
        ; ⊝-fromto = f⊝-fromto
        }
      ; _⊚_ = _f⊚_
      ; ⊚-fromto = f⊚-fromto
      }
    }

  -- Products
  private
    pCh = Ch A × Ch B
    _p⊕_ : A × B → Ch A × Ch B → A × B
    _p⊕_ (a , b) (da , db) = a ⊕ da , b ⊕ db
    _p⊝_ : A × B → A × B → pCh
    _p⊝_ (a2 , b2) (a1 , b1) = a2 ⊝ a1 , b2 ⊝ b1
    pch_from_to_ : pCh → A × B → A × B → Set
    pch (da , db) from (a1 , b1) to (a2 , b2) = ch da from a1 to a2 × ch db from b1 to b2
    _p⊚_ : pCh → pCh → pCh
    (da1 , db1) p⊚ (da2 , db2) = da1 ⊚[ A ] da2 , db1 ⊚[ B ] db2
    pfromto→⊕ : ∀ dp p1 p2 →
      pch dp from p1 to p2 → p1 p⊕ dp ≡ p2
    pfromto→⊕ (da , db) (a1 , b1) (a2 , b2) (daa , dbb) =
      cong₂ _,_ (fromto→⊕ _ _ _ daa) (fromto→⊕ _ _ _ dbb)
    p⊝-fromto : ∀ (p1 p2 : A × B) → pch p2 p⊝ p1 from p1 to p2
    p⊝-fromto (a1 , b1) (a2 , b2) = ⊝-fromto a1 a2 , ⊝-fromto b1 b2
    p⊚-fromto : ∀ p1 p2 p3 dp1 dp2 →
      pch dp1 from p1 to p2 → (pch dp2 from p2 to p3) → pch dp1 p⊚ dp2 from p1 to p3
    p⊚-fromto (a1 , b1) (a2 , b2) (a3 , b3) (da1 , db1) (da2 , db2)
      (daa1 , dbb1) (daa2 , dbb2) =
        ⊚-fromto a1 a2 a3 da1 da2 daa1 daa2 , ⊚-fromto b1 b2 b3 db1 db2 dbb1 dbb2

  instance
    pairCS : ChangeStructure (A × B)
  pairCS = record
    { Ch = pCh
    ; ch_from_to_ = pch_from_to_
    ; isCompChangeStructure = record
      { isChangeStructure = record
        { _⊕_ = _p⊕_
        ; fromto→⊕ = pfromto→⊕
        ; _⊝_ = _p⊝_
        ; ⊝-fromto = p⊝-fromto
        }
      ; _⊚_ = _p⊚_
      ; ⊚-fromto = p⊚-fromto
      }
    }

  -- Sums
  private
    SumChange = (Ch A ⊎ Ch B) ⊎ (A ⊎ B)

  data SumChange2 : Set where
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

  inv1 : ∀ ds → convert₁ (convert ds) ≡ ds
  inv1 (inj₁ (inj₁ da)) = refl
  inv1 (inj₁ (inj₂ db)) = refl
  inv1 (inj₂ s) = refl
  inv2 : ∀ ds → convert (convert₁ ds) ≡ ds
  inv2 (ch₁ da) = refl
  inv2 (ch₂ db) = refl
  inv2 (rp s) = refl

  private
    _s⊕2_ : A ⊎ B → SumChange2 → A ⊎ B
    _s⊕2_ s (rp s₁) = s₁
    _s⊕2_ (inj₁ a) (ch₁ da) = inj₁ (a ⊕ da)
    _s⊕2_ (inj₂ b) (ch₂ db) = inj₂ (b ⊕ db)
    _s⊕2_ (inj₂ b) (ch₁ da) = inj₂ b -- invalid
    _s⊕2_ (inj₁ a) (ch₂ db) = inj₁ a -- invalid

    _s⊕_ : A ⊎ B → SumChange → A ⊎ B
    s s⊕ ds = s s⊕2 (convert ds)

    _s⊝2_ : A ⊎ B → A ⊎ B → SumChange2
    _s⊝2_ (inj₁ x2) (inj₁ x1) = ch₁ (x2 ⊝ x1)
    _s⊝2_ (inj₂ y2) (inj₂ y1) = ch₂ (y2 ⊝ y1)
    _s⊝2_ s2 s1 = rp s2

    _s⊝_ : A ⊎ B → A ⊎ B → SumChange
    s2 s⊝ s1 = convert₁ (s2 s⊝2 s1)

  data sch_from_to_ : SumChange → A ⊎ B → A ⊎ B → Set where
    -- sft = Sum From To
    sft₁ : ∀ {da a1 a2} (daa : ch da from a1 to a2) → sch (convert₁ (ch₁ da)) from (inj₁ a1) to (inj₁ a2)
    sft₂ : ∀ {db b1 b2} (dbb : ch db from b1 to b2) → sch (convert₁ (ch₂ db)) from (inj₂ b1) to (inj₂ b2)
    sftrp : ∀ s1 s2 → sch (convert₁ (rp s2)) from s1 to s2

  sfromto→⊕2 : (ds : SumChange2) (s1 s2 : A ⊎ B) →
    sch convert₁ ds from s1 to s2 → s1 s⊕2 ds ≡ s2
  sfromto→⊕2 (ch₁ da) (inj₁ a1) (inj₁ a2) (sft₁ daa) = cong inj₁ (fromto→⊕ _ _ _ daa)
  sfromto→⊕2 (ch₂ db) (inj₂ b1) (inj₂ b2) (sft₂ dbb) = cong inj₂ (fromto→⊕ _ _ _ dbb)
  sfromto→⊕2 (rp .s2) .s1 .s2 (sftrp s1 s2) = refl

  sfromto→⊕ : (ds : SumChange) (s1 s2 : A ⊎ B) →
    sch ds from s1 to s2 → s1 s⊕ ds ≡ s2
  sfromto→⊕ ds s1 s2 dss =
    sfromto→⊕2 (convert ds) s1 s2
      (subst (sch_from s1 to s2) (sym (inv1 ds))
        dss)
  s⊝-fromto : (s1 s2 : A ⊎ B) → sch s2 s⊝ s1 from s1 to s2
  s⊝-fromto (inj₁ a1) (inj₁ a2) = sft₁ (⊝-fromto a1 a2)
  s⊝-fromto (inj₂ b1) (inj₂ b2) = sft₂ (⊝-fromto b1 b2)
  s⊝-fromto s1@(inj₁ a1) s2@(inj₂ b2) = sftrp s1 s2
  s⊝-fromto s1@(inj₂ b1) s2@(inj₁ a2) = sftrp s1 s2

  _s⊚2_ : SumChange2 → SumChange2 → SumChange2
  ds1 s⊚2 rp s3 = rp s3
  ch₁ da1 s⊚2 ch₁ da2 = ch₁ (da1 ⊚[ A ] da2)
  rp (inj₁ a2) s⊚2 ch₁ da2 = rp (inj₁ (a2 ⊕ da2))
  ch₂ db1 s⊚2 ch₂ db2 = ch₂ (db1 ⊚[ B ] db2)
  rp (inj₂ b2) s⊚2 ch₂ db2 = rp (inj₂ (b2 ⊕ db2))
  -- Cases for invalid combinations of input changes.
  --
  -- That is, whenever ds2 is a non-replacement change for outputs that ds1
  -- can't produce.
  --
  -- We can prove validity preservation *without* filling this in.
  ds1 s⊚2 ds2 = ds1

  _s⊚_ : SumChange → SumChange → SumChange
  ds1 s⊚ ds2 = convert₁ (convert ds1 s⊚2 convert ds2)

  s⊚-fromto : (s1 s2 s3 : A ⊎ B) (ds1 ds2 : SumChange) →
      sch ds1 from s1 to s2 →
      sch ds2 from s2 to s3 → sch ds1 s⊚ ds2 from s1 to s3

  s⊚-fromto (inj₁ a1) (inj₁ a2) (inj₁ a3) (inj₁ (inj₁ da1)) (inj₁ (inj₁ da2)) (sft₁ daa1) (sft₁ daa2) = sft₁ (⊚-fromto a1 a2 a3 _ _ daa1 daa2)
  s⊚-fromto (inj₂ b1) (inj₂ b2) (inj₂ b3) (inj₁ (inj₂ db1)) (inj₁ (inj₂ db2)) (sft₂ dbb1) (sft₂ dbb2) = sft₂ (⊚-fromto b1 b2 b3 _ _ dbb1 dbb2)
  s⊚-fromto s1 (inj₁ a2) (inj₁ a3) .(inj₂ (inj₁ _)) .(inj₁ (inj₁ _)) (sftrp .s1 .(inj₁ _)) (sft₁ daa) rewrite fromto→⊕ _ a2 a3 daa = sftrp _ _
  s⊚-fromto s1 (inj₂ b2) (inj₂ b3) .(inj₂ (inj₂ _)) .(inj₁ (inj₂ _)) (sftrp .s1 .(inj₂ _)) (sft₂ dbb) rewrite fromto→⊕ _ b2 b3 dbb = sftrp _ _
  s⊚-fromto s1 s2 s3 _ _ _ (sftrp .s2 .s3) = sftrp s1 s3

  -- s⊚-fromto .(inj₂ b1) .(inj₁ a2) (inj₁ a3) .(inj₂ (inj₁ a2)) (inj₁ (inj₁ da2)) (sftrp (inj₂ b1) (inj₁ a2)) (sft₁ daa2) with sfromto→⊕ (inj₁ (inj₁ da2)) _ _ (sft₁ daa2)
  -- s⊚-fromto .(inj₂ b1) .(inj₁ a2) (inj₁ .(a2 ⊕ da2)) .(inj₂ (inj₁ a2)) (inj₁ (inj₁ da2)) (sftrp (inj₂ b1) (inj₁ a2)) (sft₁ daa2) | refl = sftrp (inj₂ b1) (inj₁ (a2 ⊕ da2))
  -- s⊚-fromto .(inj₁ a1) .(inj₂ b2) (inj₂ b3) .(inj₂ (inj₂ b2)) (inj₁ (inj₂ db2)) (sftrp (inj₁ a1) (inj₂ b2)) (sft₂ dbb2) with sfromto→⊕ (inj₁ (inj₂ db2)) _ _ (sft₂ dbb2)
  -- s⊚-fromto .(inj₁ a1) .(inj₂ b2) (inj₂ .(b2 ⊕ db2)) .(inj₂ (inj₂ b2)) (inj₁ (inj₂ db2)) (sftrp (inj₁ a1) (inj₂ b2)) (sft₂ dbb2) | refl = sftrp (inj₁ a1) (inj₂ (b2 ⊕ db2))

  instance
    sumCS : ChangeStructure (A ⊎ B)
  sumCS = record
    { Ch = SumChange
    ; ch_from_to_ = sch_from_to_
    ; isCompChangeStructure = record
      { isChangeStructure = record
      { _⊕_ = _s⊕_
      ; fromto→⊕ = sfromto→⊕
      ; _⊝_ = _s⊝_
      ; ⊝-fromto = s⊝-fromto
      }
      ; _⊚_ = _s⊚_
      ; ⊚-fromto = s⊚-fromto
      }
    }

instance
  unitCS : ChangeStructure ⊤

  unitCS = record
    { Ch = ⊤
    ; ch_from_to_ = λ dv v1 v2 → ⊤
    ; isCompChangeStructure = record
      { isChangeStructure = record
      { _⊕_ = λ _ _ → tt
      ; fromto→⊕ = λ { _ _ tt _ → refl }
      ; _⊝_ = λ _ _ → tt
      ; ⊝-fromto = λ a b → tt
      }
      ; _⊚_ = λ da1 da2 → tt
      ; ⊚-fromto = λ a1 a2 a3 da1 da2 daa1 daa2 → tt
      }
    }
