module Thesis.Changes where

open import Thesis.Lang
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- record BasicChangeStructure (A : Set) : Set₁ where
--   field
--     Ch : Set
--     ch_from_to_ : (dv : Ch) → (v1 v2 : A) → Set

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

record IsCompChangeStructure (A : Set) (ChA : Set) (ch_from_to_ : (dv : ChA) → (v1 v2 : A) → Set) : Set₁ where
  field
    isChangeStructure : IsChangeStructure A ChA ch_from_to_
    _⊚[_]_ : ChA → A → ChA → ChA
    ⊚-fromto : ∀ (a1 a2 a3 : A) (da1 da2 : ChA) →
      ch da1 from a1 to a2 → ch da2 from a2 to a3 → ch da1 ⊚[ a1 ] da2 from a1 to a3

  open IsChangeStructure isChangeStructure public
  ⊚-correct : ∀ (a1 a2 a3 : A) (da1 da2 : ChA) →
    ch da1 from a1 to a2 → ch da2 from a2 to a3 →
    a1 ⊕ (da1 ⊚[ a1 ] da2) ≡ a3
  ⊚-correct a1 a2 a3 da1 da2 daa1 daa2 = fromto→⊕ _ _ _ (⊚-fromto _ _ _ da1 da2 daa1 daa2)

IsChangeStructure→IsCompChangeStructure : ∀ {A ChA ch_from_to_} → IsChangeStructure A ChA ch_from_to_ → IsCompChangeStructure A ChA ch_from_to_
IsChangeStructure→IsCompChangeStructure {A} {ChA} {ch_from_to_} isCS = record
  { isChangeStructure = isCS
  ; _⊚[_]_ = λ da1 a da2 → a ⊕ da1 ⊕ da2 ⊝ a
  ; ⊚-fromto = body
  }
  where
    _⊕_ = IsChangeStructure._⊕_ isCS
    _⊝_ = IsChangeStructure._⊝_ isCS
    fromto→⊕ = IsChangeStructure.fromto→⊕ isCS
    ⊝-fromto = IsChangeStructure.⊝-fromto isCS
    infixl 6 _⊕_ _⊝_
    body : ∀ (a1 a2 a3 : A) da1 da2 →
      ch da1 from a1 to a2 →
      ch da2 from a2 to a3 → ch a1 ⊕ da1 ⊕ da2 ⊝ a1 from a1 to a3
    body a1 a2 a3 da1 da2 daa1 daa2 rewrite fromto→⊕ _ _ _ daa1 | fromto→⊕ _ _ _ daa2 =
      ⊝-fromto a1 a3


record ChangeStructure (A : Set) : Set₁ where
  field
    Ch : Set
    ch_from_to_ : (dv : Ch) → (v1 v2 : A) → Set
    -- isChangeStructure : IsChangeStructure A Ch ch_from_to_
  -- open IsChangeStructure isChangeStructure public
    isCompChangeStructure : IsCompChangeStructure A Ch ch_from_to_
  open IsCompChangeStructure isCompChangeStructure public

open ChangeStructure {{...}} public hiding (Ch)
Ch : ∀ (A : Set) → {{CA : ChangeStructure A}} → Set
Ch A {{CA}} = ChangeStructure.Ch CA

-- instance
--   iCsToBCS : ∀ {A} {{CA : ChangeStructure A}} → BasicChangeStructure A
--   iCsToBCS {A} {{CA}} = record
--     { Ch = ChangeStructure.Ch CA
--     ; ch_from_to_ = ChangeStructure.ch_from_to_ CA
--     }

{-# DISPLAY IsChangeStructure._⊕_ x = _⊕_ #-}
{-# DISPLAY ChangeStructure._⊕_ x = _⊕_ #-}
{-# DISPLAY IsChangeStructure._⊝_ x = _⊝_ #-}
{-# DISPLAY ChangeStructure._⊝_ x = _⊝_ #-}
{-# DISPLAY IsChangeStructure.nil x = nil #-}
{-# DISPLAY ChangeStructure.nil x = nil #-}
{-# DISPLAY IsCompChangeStructure._⊚[_]_ x = _⊚[_]_ #-}
{-# DISPLAY ChangeStructure._⊚[_]_ x = _⊚[_]_ #-}
{-# DISPLAY ChangeStructure.ch_from_to_ x = ch_from_to_ #-}

module _ {A B : Set} {{CA : ChangeStructure A}} {{CB : ChangeStructure B}} where
  open ≡-Reasoning
  open import Postulate.Extensionality
  instance
    funCS : ChangeStructure (A → B)
  infixl 6 _f⊕_ _f⊝_
  private
    fCh = A → Ch A → Ch B
    _f⊕_ : (A → B) → fCh → A → B
    _f⊕_ = λ f df a → f a ⊕ df a (nil a)
    _f⊝_ : (g f : A → B) → fCh
    _f⊝_ = λ g f a da → g (a ⊕ da) ⊝ f a
    _f⊚[_]_ : fCh → (A → B) → fCh → fCh
    _f⊚[_]_ df1 f df2 = λ a da → (df1 a (nil a)) ⊚[ f a ] (df2 a da)
    -- f⊚2 : fCh → (A → B) → fCh → fCh
    fCh_from_to_ : (df : fCh) → (f1 f2 : A → B) → Set
    fCh_from_to_ =
      λ df f1 f2 → ∀ da (a1 a2 : A) (daa : ch da from a1 to a2) →
        ch df a1 da from f1 a1 to f2 a2

    f⊝-fromto : ∀ (f1 f2 : A → B) → fCh (f2 f⊝ f1) from f1 to f2
    f⊝-fromto f1 f2 da a1 a2 daa
      rewrite sym (fromto→⊕ da a1 a2 daa) = ⊝-fromto (f1 a1) (f2 (a1 ⊕ da))
    f⊚-fromto : ∀ (f1 f2 f3 : A → B) (df1 df2 : fCh) → fCh df1 from f1 to f2 → fCh df2 from f2 to f3 →
      fCh df1 f⊚[ f1 ] df2 from f1 to f3
    f⊚-fromto f1 f2 f3 df1 df2 dff1 dff2 da a1 a2 daa = ⊚-fromto (f1 a1) (f2 a1) (f3 a2)  (df1 a1 (nil a1)) (df2 a1 da) (dff1 (nil a1) a1 a1 (nil-fromto a1)) (dff2 da a1 a2 daa)
      -- ⊚-fromto (f a1) (df1 a1 (nil a1))
      --   (dff1 (nil a1) a1 a1 (nil-fromto a1))
      --   (df2 a1 da)
      -- dff1 (nil a1) a1 a1 (nil-fromto a1)


    -- f⊚-fromto3 : ∀ (f : A → B) (df1 : fCh) → fCh df1 from f to (f f⊕ df1) → (df2 : fCh) → fCh df2 from (f f⊕ df1) to (f f⊕ df1 f⊕ df2) →
    --   fCh df1 f⊚[ f ] df2 from f to (f f⊕ df1 f⊕ df2)
    -- f⊚-fromto3 f df1 dff1 df2 dff2 da a1 a2 daa = lemma
    --   where
    --     foo : f a2 ⊕ df1 a2 (nil a2) ⊕ df2 a2 (nil a2) ≡ f a1 ⊕ df1 a1 (nil a1) ⊕ df2 a1 da
    --     foo = ?
    --     bar : ch df2 a1 da from f a1 ⊕ df1 a1 (nil a1) to
    --       (f a1 ⊕ df1 a1 (nil a1) ⊕ df2 a1 da)
    --     bar rewrite sym foo = dff2 da a1 a2 daa
    --     lemma : ch (df1 f⊚[ f ] df2) a1 da from f a1 to (f f⊕ df1 f⊕ df2) a2
    --     lemma rewrite foo =
    --       ⊚-fromto (f a1) (df1 a1 (nil a1))
    --         (dff1 (nil a1) a1 a1 (nil-fromto a1)) (df2 a1 da)
    --         bar
    --   -- ⊚-fromto (f a1) (df1 a1 (nil a1))
    --   --   (dff1 (nil a1) a1 a1 (nil-fromto a1))
    --   --   (df2 a1 da)
    --   -- dff1 (nil a1) a1 a1 (nil-fromto a1)

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
      ; _⊚[_]_ = _f⊚[_]_
      ; ⊚-fromto = f⊚-fromto
      }
    }
  private
    pCh = Ch A × Ch B
    _p⊕_ : A × B → Ch A × Ch B → A × B
    _p⊕_ (a , b) (da , db) = a ⊕ da , b ⊕ db
    _p⊝_ : A × B → A × B → pCh
    _p⊝_ (a2 , b2) (a1 , b1) = a2 ⊝ a1 , b2 ⊝ b1
    pch_from_to_ : pCh → A × B → A × B → Set
    pch (da , db) from (a1 , b1) to (a2 , b2) = ch da from a1 to a2 × ch db from b1 to b2
    _p⊚[_]_ : pCh → A × B → pCh → pCh
    (da1 , db1) p⊚[ a , b ] (da2 , db2) = da1 ⊚[ a ] da2 , db1 ⊚[ b ] db2
    pfromto→⊕ : ∀ dp p1 p2 →
      pch dp from p1 to p2 → p1 p⊕ dp ≡ p2
    pfromto→⊕ (da , db) (a1 , b1) (a2 , b2) (daa , dbb) =
      cong₂ _,_ (fromto→⊕ _ _ _ daa) (fromto→⊕ _ _ _ dbb)
    p⊝-fromto : ∀ (p1 p2 : A × B) → pch p2 p⊝ p1 from p1 to p2
    p⊝-fromto (a1 , b1) (a2 , b2) = ⊝-fromto a1 a2 , ⊝-fromto b1 b2
    p⊚-fromto : ∀ p1 p2 p3 dp1 dp2 →
      pch dp1 from p1 to p2 → (pch dp2 from p2 to p3) → pch dp1 p⊚[ p1 ] dp2 from p1 to p3
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
      ; _⊚[_]_ = _p⊚[_]_
      ; ⊚-fromto = p⊚-fromto
      }
    }
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
    _s⊕2_ (inj₁ a) (ch₁ da) = inj₁ (a ⊕ da)
    _s⊕2_ (inj₂ b) (ch₂ db) = inj₂ (b ⊕ db)
    _s⊕2_ (inj₂ b) (ch₁ da) = inj₂ b -- invalid
    _s⊕2_ (inj₁ a) (ch₂ db) = inj₁ a -- invalid
    _s⊕2_ s (rp s₁) = s₁

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
    sftrp₁ : ∀ a1 b2 → sch (convert₁ (rp (inj₂ b2))) from (inj₁ a1) to (inj₂ b2)
    sftrp₂ : ∀ b1 a2 → sch (convert₁ (rp (inj₁ a2))) from (inj₂ b1) to (inj₁ a2)

  sfromto→⊕2 : (ds : SumChange2) (s1 s2 : A ⊎ B) →
    sch convert₁ ds from s1 to s2 → s1 s⊕2 ds ≡ s2
  sfromto→⊕2 (ch₁ da) (inj₁ a1) (inj₁ a2) (sft₁ daa) = cong inj₁ (fromto→⊕ _ _ _ daa)
  sfromto→⊕2 (ch₂ db) (inj₂ b1) (inj₂ b2) (sft₂ dbb) = cong inj₂ (fromto→⊕ _ _ _ dbb)
  sfromto→⊕2 (rp .(inj₂ y)) (inj₁ x) (inj₂ y) (sftrp₁ .x .y) = refl
  sfromto→⊕2 (rp .(inj₁ x)) (inj₂ y) (inj₁ x) (sftrp₂ .y .x) = refl

  sfromto→⊕ : (ds : SumChange) (s1 s2 : A ⊎ B) →
    sch ds from s1 to s2 → s1 s⊕ ds ≡ s2
    -- rewrite sym (inv1 ds)
  sfromto→⊕ ds s1 s2 dss =
    sfromto→⊕2 (convert ds) s1 s2
      (subst (sch_from s1 to s2) (sym (inv1 ds))
        dss)
  s⊝-fromto : (s1 s2 : A ⊎ B) → sch s2 s⊝ s1 from s1 to s2
  s⊝-fromto (inj₁ a1) (inj₁ a2) = sft₁ (⊝-fromto a1 a2)
  s⊝-fromto (inj₁ a1) (inj₂ b2) = sftrp₁ a1 b2
  s⊝-fromto (inj₂ b1) (inj₁ a2) = sftrp₂ b1 a2
  s⊝-fromto (inj₂ b1) (inj₂ b2) = sft₂ (⊝-fromto b1 b2)
  instance
    sumCS : ChangeStructure (A ⊎ B)
  sumCS = record
    { Ch = SumChange
    ; ch_from_to_ = sch_from_to_
    ; isCompChangeStructure = IsChangeStructure→IsCompChangeStructure (record
      { _⊕_ = _s⊕_
      ; fromto→⊕ = sfromto→⊕
      ; _⊝_ = _s⊝_
      ; ⊝-fromto = s⊝-fromto
      })
    }

open import Data.Integer
open import Data.Unit
open import Theorem.Groups-Nehemiah
private
  intCh = ℤ
instance
  intCS : ChangeStructure ℤ
intCS = record
  { Ch = ℤ
  ; ch_from_to_ = λ dv v1 v2 → v1 + dv ≡ v2
  ; isCompChangeStructure = record
    { isChangeStructure = record
      { _⊕_ = _+_
      ; fromto→⊕ = λ dv v1 v2 v2≡v1+dv → v2≡v1+dv
      ; _⊝_ = _-_
      ; ⊝-fromto = λ a b → n+[m-n]=m {a} {b}
      }
    ; _⊚[_]_ = λ da1 a da2 → da1 + da2
    ; ⊚-fromto = i⊚-fromto
    }
  }
  where
    i⊚-fromto : (a1 a2 a3 : ℤ) (da1 da2 : intCh) →
      a1 + da1 ≡ a2 → a2 + da2 ≡ a3 → a1 + (da1 + da2) ≡ a3
    i⊚-fromto a1 a2 a3 da1 da2 a1+da1≡a2 a2+da2≡a3
      rewrite sym (associative-int a1 da1 da2) | a1+da1≡a2 = a2+da2≡a3

Chτ : (τ : Type) → Set
Chτ τ = ⟦ Δt τ ⟧Type

ΔΓ : Context → Context
ΔΓ ∅ = ∅
ΔΓ (τ • Γ) = Δt τ • τ • ΔΓ Γ

ChΓ : ∀ (Γ : Context) → Set
ChΓ Γ = ⟦ ΔΓ Γ ⟧Context

[_]τ_from_to_ : ∀ (τ : Type) → (dv : Chτ τ) → (v1 v2 : ⟦ τ ⟧Type) → Set

isCompChangeStructureτ : ∀ τ → IsCompChangeStructure ⟦ τ ⟧Type ⟦ Δt τ ⟧Type [ τ ]τ_from_to_

changeStructureτ : ∀ τ → ChangeStructure ⟦ τ ⟧Type
changeStructureτ τ = record { isCompChangeStructure = isCompChangeStructureτ τ }

instance
  ichangeStructureτ : ∀ {τ} → ChangeStructure ⟦ τ ⟧Type
  ichangeStructureτ {τ} = changeStructureτ τ

[ σ ⇒ τ ]τ df from f1 to f2 =
  ∀ (da : Chτ σ) (a1 a2 : ⟦ σ ⟧Type) →
  [ σ ]τ da from a1 to a2 → [ τ ]τ df a1 da from f1 a1 to f2 a2
[ int ]τ dv from v1 to v2 = v1 + dv ≡ v2
[ pair σ τ ]τ (da , db) from (a1 , b1) to (a2 , b2) = [ σ ]τ da from a1 to a2 × [ τ ]τ db from b1 to b2
[ sum σ τ ]τ dv from v1 to v2 = sch_from_to_ dv v1 v2

isCompChangeStructureτ (σ ⇒ τ) = ChangeStructure.isCompChangeStructure (funCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ int = ChangeStructure.isCompChangeStructure intCS
isCompChangeStructureτ (pair σ τ) = ChangeStructure.isCompChangeStructure (pairCS {{changeStructureτ σ}} {{changeStructureτ τ}})
isCompChangeStructureτ (sum σ τ) = ChangeStructure.isCompChangeStructure ((sumCS {{changeStructureτ σ}} {{changeStructureτ τ}}))

data [_]Γ_from_to_ : ∀ Γ → ChΓ Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set where
  v∅ : [ ∅ ]Γ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Γ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ]τ dv from v1 to v2) →
    (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
    [ τ • Γ ]Γ (dv • v1 • dρ) from (v1 • ρ1) to (v2 • ρ2)

module _ where
  _e⊕_ : ∀ {Γ} → ⟦ Γ ⟧Context → ChΓ Γ → ⟦ Γ ⟧Context
  _e⊕_ ∅ ∅ = ∅
  _e⊕_ (v • ρ) (dv • _ • dρ) = v ⊕ dv • ρ e⊕ dρ
  _e⊝_ : ∀ {Γ} → ⟦ Γ ⟧Context → ⟦ Γ ⟧Context → ChΓ Γ
  _e⊝_ ∅ ∅ = ∅
  _e⊝_ (v₂ • ρ₂) (v₁ • ρ₁) = v₂ ⊝ v₁ • v₁ • ρ₂ e⊝ ρ₁

  isEnvCompCS : ∀ Γ → IsCompChangeStructure ⟦ Γ ⟧Context (ChΓ Γ) [ Γ ]Γ_from_to_

  efromto→⊕ : ∀ {Γ} (dρ : ChΓ Γ) (ρ1 ρ2 : ⟦ Γ ⟧Context) →
      [ Γ ]Γ dρ from ρ1 to ρ2 → (ρ1 e⊕ dρ) ≡ ρ2
  efromto→⊕ .∅ .∅ .∅ v∅ = refl
  efromto→⊕ .(_ • _ • _) .(_ • _) .(_ • _) (dvv v• dρρ) =
    cong₂ _•_ (fromto→⊕ _ _ _ dvv) (efromto→⊕ _ _ _ dρρ)

  e⊝-fromto : ∀ {Γ} → (ρ1 ρ2 : ⟦ Γ ⟧Context) → [ Γ ]Γ ρ2 e⊝ ρ1 from ρ1 to ρ2
  e⊝-fromto ∅ ∅ = v∅
  e⊝-fromto (v1 • ρ1) (v2 • ρ2) = ⊝-fromto v1 v2 v• e⊝-fromto ρ1 ρ2

  isEnvCompCS Γ = IsChangeStructure→IsCompChangeStructure (record
    { _⊕_ = _e⊕_
    ; fromto→⊕ = efromto→⊕
    ; _⊝_ = _e⊝_
    ; ⊝-fromto = e⊝-fromto
    } )

changeStructureΓ : ∀ Γ → ChangeStructure ⟦ Γ ⟧Context
changeStructureΓ Γ = record { isCompChangeStructure = isEnvCompCS Γ }

instance
  ichangeStructureΓ : ∀ {Γ} → ChangeStructure ⟦ Γ ⟧Context
  ichangeStructureΓ {Γ} = changeStructureΓ Γ
