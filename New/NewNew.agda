module New.NewNew where

open import New.Changes
open import New.LangChanges
open import New.Lang
open import New.Derive
open import Data.Empty

[_]_from_to_ : ∀ (τ : Type) → (dv : Cht τ) → (v1 v2 : ⟦ τ ⟧Type) → Set

-- This can't be a datatype, since it wouldn't be strictly positive as it
-- appears on the left of an arrow in the function case, which then can be
-- contained in nested "fromto-validity" proofs.
sumfromto : ∀ (σ τ : Type) → (dv : SumChange2 {A = ⟦ σ ⟧Type} {B = ⟦ τ ⟧Type}) → (v1 v2 : ⟦ sum σ τ ⟧Type) → Set
sumfromto σ τ (ch₁ da) (inj₁ a1) (inj₁ a2) = [ σ ] da from a1 to a2
-- These fallback equations unfortunately don't hold definitionally, they're
-- split on multiple cases, so the pattern match is a mess.
--
-- To "case split" on validity, I typically copy-paste the pattern match from
-- fromto→⊕ and change the function name :-(.
sumfromto σ τ (ch₁ da) _ _ = ⊥
sumfromto σ τ (ch₂ db) (inj₂ b1) (inj₂ b2) = [ τ ] db from b1 to b2
sumfromto σ τ (ch₂ db) _ _ = ⊥
sumfromto σ τ (rp (inj₂ b2)) (inj₁ a1) (inj₂ b2') = b2 ≡ b2'
sumfromto σ τ (rp (inj₁ a2)) (inj₂ b1) (inj₁ a2') = a2 ≡ a2'
sumfromto σ τ (rp s) _ _ = ⊥

[ σ ⇒ τ ] df from f1 to f2 =
  ∀ (da : Cht σ) (a1 a2 : ⟦ σ ⟧Type) →
  [ σ ] da from a1 to a2 → [ τ ] df a1 da from f1 a1 to f2 a2
[ int ] dv from v1 to v2 = v2 ≡ v1 + dv
[ pair σ τ ] (da , db) from (a1 , b1) to (a2 , b2) = [ σ ] da from a1 to a2 × [ τ ] db from b1 to b2
[ sum σ τ ] dv from v1 to v2 = sumfromto σ τ (convert dv) v1 v2

data [_]Γ_from_to_ : ∀ Γ → eCh Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set where
  v∅ : [ ∅ ]Γ ∅ from ∅ to ∅
  _v•_ : ∀ {τ Γ dv v1 v2 dρ ρ1 ρ2} →
    (dvv : [ τ ] dv from v1 to v2) →
    (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
    [ τ • Γ ]Γ (dv • v1 • dρ) from (v1 • ρ1) to (v2 • ρ2)

⟦Γ≼ΔΓ⟧ : ∀ {Γ ρ1 ρ2 dρ} → (dρρ : [ Γ ]Γ dρ from ρ1 to ρ2) →
  ρ1 ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ v∅ = refl
⟦Γ≼ΔΓ⟧ (dvv v• dρρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ dρρ)

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  ∀ {dρ ρ1 ρ2} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ t ⟧Term ρ1 ≡ ⟦ fit t ⟧Term dρ
fit-sound t dρρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ dρρ))
  (sym (weaken-sound t _))

-- Now relate this validity with ⊕. To know that nil and so on are valid, also
-- relate it to the other definition.

fromto→⊕ : ∀ {τ} dv v1 v2 →
  [ τ ] dv from v1 to v2 →
  v1 ⊕ dv ≡ v2

⊝-fromto : ∀ {τ} (v1 v2 : ⟦ τ ⟧Type) → [ τ ] v2 ⊝ v1 from v1 to v2
⊝-fromto {σ ⇒ τ} f1 f2 da a1 a2 daa rewrite sym (fromto→⊕ da a1 a2 daa) = ⊝-fromto (f1 a1) (f2 (a1 ⊕ da))
⊝-fromto {int} v1 v2 = sym (update-diff v2 v1)
⊝-fromto {pair σ τ} (a1 , b1) (a2 , b2) = ⊝-fromto a1 a2 , ⊝-fromto b1 b2
⊝-fromto {sum σ τ} (inj₁ a1) (inj₁ a2) = ⊝-fromto a1 a2
⊝-fromto {sum σ τ} (inj₁ a1) (inj₂ b2) = refl
⊝-fromto {sum σ τ} (inj₂ b1) (inj₁ a2) = refl
⊝-fromto {sum σ τ} (inj₂ b1) (inj₂ b2) = ⊝-fromto b1 b2

nil-fromto : ∀ {τ} (v : ⟦ τ ⟧Type) → [ τ ] nil v from v to v
nil-fromto v = ⊝-fromto v v

fromto→⊕ {σ ⇒ τ} df f1 f2 dff =
  ext (λ v → fromto→⊕ {τ} (df v (nil v)) (f1 v) (f2 v) (dff (nil v) v v (nil-fromto v)))
fromto→⊕ {int} dn n1 n2 refl = refl
fromto→⊕ {pair σ τ} (da , db) (a1 , b1) (a2 , b2) (daa , dbb) =
  cong₂ _,_ (fromto→⊕ _ _ _ daa) (fromto→⊕ _ _ _ dbb)
fromto→⊕ {sum σ τ} (inj₁ (inj₁ da)) (inj₁ a1) (inj₁ a2) daa rewrite fromto→⊕ da a1 a2 daa = refl
fromto→⊕ {sum σ τ} (inj₁ (inj₁ da)) (inj₁ _) (inj₂ _) ()
fromto→⊕ {sum σ τ} (inj₁ (inj₁ da)) (inj₂ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₁ (inj₁ da)) (inj₂ _) (inj₂ _) ()
fromto→⊕ {sum σ τ} (inj₁ (inj₂ db)) (inj₂ b1) (inj₂ b2) dbb rewrite fromto→⊕ db b1 b2 dbb = refl
fromto→⊕ {sum σ τ} (inj₁ (inj₂ db)) (inj₁ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₁ (inj₂ db)) (inj₁ _) (inj₂ _) ()
fromto→⊕ {sum σ τ} (inj₁ (inj₂ db)) (inj₂ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₁ a2)) (inj₂ b1) (inj₁ .a2) refl = refl
fromto→⊕ {sum σ τ} (inj₂ (inj₁ a2)) (inj₁ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₁ a2)) (inj₁ _) (inj₂ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₁ a2)) (inj₂ _) (inj₂ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₂ b2)) (inj₁ a1) (inj₂ .b2) refl = refl
fromto→⊕ {sum σ τ} (inj₂ (inj₂ b2)) (inj₁ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₂ b2)) (inj₂ _) (inj₁ _) ()
fromto→⊕ {sum σ τ} (inj₂ (inj₂ b2)) (inj₂ _) (inj₂ _) ()

fromtoDeriveConst : ∀ {τ} c →
  [ τ ] ⟦ deriveConst c ⟧Term ∅ from ⟦ c ⟧Const to ⟦ c ⟧Const
fromtoDeriveConst plus da a1 a2 daa db b1 b2 dbb rewrite daa | dbb = mn·pq=mp·nq {a1} {da} {b1} {db}
fromtoDeriveConst minus da a1 a2 daa db b1 b2 dbb rewrite daa | dbb | sym (-m·-n=-mn {b1} {db}) = mn·pq=mp·nq {a1} {da} { - b1} { - db}
fromtoDeriveConst cons da a1 a2 daa db b1 b2 dbb = daa , dbb
fromtoDeriveConst fst (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = daa
fromtoDeriveConst snd (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = dbb
fromtoDeriveConst linj da a1 a2 daa = daa
fromtoDeriveConst rinj db b1 b2 dbb = dbb
fromtoDeriveConst match (inj₁ (inj₁ da)) (inj₁ a1) (inj₁ a2) daa df f1 f2 dff dg g1 g2 dgg = dff da a1 a2 daa
fromtoDeriveConst match (inj₁ (inj₁ da)) (inj₁ _) (inj₂ _) ()
fromtoDeriveConst match (inj₁ (inj₁ da)) (inj₂ _) (inj₁ _) ()
fromtoDeriveConst match (inj₁ (inj₁ da)) (inj₂ _) (inj₂ _) ()
fromtoDeriveConst match (inj₁ (inj₂ db)) (inj₂ b1) (inj₂ b2) dbb df f1 f2 dff dg g1 g2 dgg = dgg db b1 b2 dbb
fromtoDeriveConst match (inj₁ (inj₂ db)) (inj₁ _) (inj₁ _) ()
fromtoDeriveConst match (inj₁ (inj₂ db)) (inj₁ _) (inj₂ _) ()
fromtoDeriveConst match (inj₁ (inj₂ db)) (inj₂ _) (inj₁ _) ()
fromtoDeriveConst match (inj₂ (inj₁ a2)) (inj₂ b1) (inj₁ .a2) refl df f1 f2 dff dg g1 g2 dgg rewrite changeMatchSem-lem2 f1 df g1 dg b1 a2 | sym (fromto→⊕ df _ _ dff) | sym (fromto→⊕ dg _ _ dgg) = ⊝-fromto (g1 b1) ((f1 ⊕ df) a2)
fromtoDeriveConst match (inj₂ (inj₁ a2)) (inj₁ _) (inj₁ _) ()
fromtoDeriveConst match (inj₂ (inj₁ a2)) (inj₁ _) (inj₂ _) ()
fromtoDeriveConst match (inj₂ (inj₁ a2)) (inj₂ _) (inj₂ _) ()
fromtoDeriveConst match (inj₂ (inj₂ b2)) (inj₁ a1) (inj₂ .b2) refl df f1 f2 dff dg g1 g2 dgg rewrite changeMatchSem-lem1 f1 df g1 dg a1 b2 | sym (fromto→⊕ df _ _ dff) | sym (fromto→⊕ dg _ _ dgg) = ⊝-fromto (f1 a1) ((g1 ⊕ dg) b2)
fromtoDeriveConst match (inj₂ (inj₂ b2)) (inj₁ _) (inj₁ _) ()
fromtoDeriveConst match (inj₂ (inj₂ b2)) (inj₂ _) (inj₁ _) ()
fromtoDeriveConst match (inj₂ (inj₂ b2)) (inj₂ _) (inj₂ _) ()

fromtoDeriveVar : ∀ {Γ τ} → (x : Var Γ τ) →
  ∀ {dρ ρ1 ρ2}  → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ] (⟦ x ⟧ΔVar ρ1 dρ) from (⟦ x ⟧Var ρ1) to (⟦ x ⟧Var ρ2)
fromtoDeriveVar this (dvv v• dρρ) = dvv
fromtoDeriveVar (that x) (dvv v• dρρ) = fromtoDeriveVar x dρρ

fromtoDerive : ∀ {Γ} τ → (t : Term Γ τ) →
  {dρ : eCh Γ} {ρ1 ρ2 : ⟦ Γ ⟧Context} → [ Γ ]Γ dρ from ρ1 to ρ2 →
    [ τ ] (⟦ t ⟧ΔTerm ρ1 dρ) from (⟦ t ⟧Term ρ1) to (⟦ t ⟧Term ρ2)
fromtoDerive τ (const c) {dρ} {ρ1} dρρ rewrite ⟦ c ⟧ΔConst-rewrite ρ1 dρ = fromtoDeriveConst c
fromtoDerive τ (var x) dρρ = fromtoDeriveVar x dρρ
fromtoDerive τ (app {σ} s t) dρρ rewrite sym (fit-sound t dρρ) =
  let fromToF = fromtoDerive (σ ⇒ τ) s dρρ
  in let fromToB = fromtoDerive σ t dρρ in fromToF _ _ _ fromToB
fromtoDerive (σ ⇒ τ) (abs t) dρρ = λ dv v1 v2 dvv →
  fromtoDerive τ t (dvv v• dρρ)

open import Postulate.Extensionality

open ≡-Reasoning

-- If df is valid, prove (f1 ⊕ df) (a ⊕ da) ≡ f1 a ⊕ df a da.

-- This statement uses a ⊕ da instead of a2, which is not the style of this formalization but fits better with the other one.
-- Instead, WellDefinedFunChangeFromTo (without prime) fits this formalization.
WellDefinedFunChangeFromTo′ : ∀ {σ τ} (f1 : ⟦ σ ⇒ τ ⟧Type) → (df : Cht (σ ⇒ τ)) → Set
WellDefinedFunChangeFromTo′ f1 df = ∀ da a → [ _ ] da from a to (a ⊕ da) → WellDefinedFunChangePoint f1 df a da

fromto→WellDefined′ : ∀ {σ τ f1 f2 df} → [ σ ⇒ τ ] df from f1 to f2 →
  WellDefinedFunChangeFromTo′ f1 df
fromto→WellDefined′ {f1 = f1} {f2} {df} dff da a daa =
  begin
    (f1 ⊕ df) (a ⊕ da)
  ≡⟨⟩
    f1 (a ⊕ da) ⊕ df (a ⊕ da) (nil (a ⊕ da))
  ≡⟨ (fromto→⊕
     (df (a ⊕ da) (nil (a ⊕ da))) _ _
     (dff (nil (a ⊕ da)) _ _ (nil-fromto (a ⊕ da))))
  ⟩
    f2 (a ⊕ da)
  ≡⟨ sym (fromto→⊕ _ _ _ (dff da _ _ daa)) ⟩
    f1 a ⊕ df a da
  ∎

WellDefinedFunChangeFromTo : ∀ {σ τ} (f1 : ⟦ σ ⇒ τ ⟧Type) → (df : Cht (σ ⇒ τ)) → Set
WellDefinedFunChangeFromTo f1 df = ∀ da a1 a2 → [ _ ] da from a1 to a2 → WellDefinedFunChangePoint f1 df a1 da

fromto→WellDefined : ∀ {σ τ f1 f2 df} → [ σ ⇒ τ ] df from f1 to f2 →
  WellDefinedFunChangeFromTo f1 df
fromto→WellDefined {f1 = f1} {f2} {df} dff da a1 a2 daa =
  fromto→WellDefined′ dff da a1 daa′
  where
    daa′ : [ _ ] da from a1 to (a1 ⊕ da)
    daa′ rewrite fromto→⊕ da _ _ daa = daa

-- Recursive isomorphism between the two validities.
--
-- Among other things, valid→fromto proves that a validity-preserving function,
-- with validity defined via (f1 ⊕ df) (a ⊕ da) ≡ f1 a ⊕ df a da, is also valid
-- in the "fromto" sense.
--
-- We can't hope for a better statement, since we need the equation to be
-- satisfied also by returned or argument functions.

fromto→valid : ∀ {τ} →
  ∀ dv v1 v2 → [ τ ] dv from v1 to v2 →
  valid v1 dv
valid→fromto : ∀ {τ} v (dv : Cht τ) → valid v dv → [ τ ] dv from v to (v ⊕ dv)

fromto→valid {int} = λ dv v1 v2 x → tt
fromto→valid {pair σ τ} (da , db) (a1 , b1) (a2 , b2) (daa , dbb) = (fromto→valid da _ _ daa) , (fromto→valid db _ _ dbb)
fromto→valid {σ ⇒ τ} df f1 f2 dff = λ a da ada →
  fromto→valid (df a da) (f1 a) (f2 (a ⊕ da)) (dff da a (a ⊕ da) (valid→fromto a da ada)) ,
  fromto→WellDefined′ dff da a (valid→fromto a da ada)
fromto→valid {sum σ τ} (inj₁ (inj₁ da)) (inj₁ a1) (inj₁ a2) daa = sv₁ a1 da (fromto→valid da a1 a2 daa)
fromto→valid {sum σ τ} (inj₁ (inj₁ da)) (inj₁ _) (inj₂ _) ()
fromto→valid {sum σ τ} (inj₁ (inj₁ da)) (inj₂ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₁ (inj₁ da)) (inj₂ _) (inj₂ _) ()
fromto→valid {sum σ τ} (inj₁ (inj₂ db)) (inj₂ b1) (inj₂ b2) dbb = sv₂ b1 db (fromto→valid db b1 b2 dbb)
fromto→valid {sum σ τ} (inj₁ (inj₂ db)) (inj₁ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₁ (inj₂ db)) (inj₁ _) (inj₂ _) ()
fromto→valid {sum σ τ} (inj₁ (inj₂ db)) (inj₂ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₁ a2)) (inj₂ b1) (inj₁ .a2) refl = svrp₂ b1 a2
fromto→valid {sum σ τ} (inj₂ (inj₁ a2)) (inj₁ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₁ a2)) (inj₁ _) (inj₂ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₁ a2)) (inj₂ _) (inj₂ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₂ b2)) (inj₁ a1) (inj₂ .b2) refl = svrp₁ a1 b2
fromto→valid {sum σ τ} (inj₂ (inj₂ b2)) (inj₁ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₂ b2)) (inj₂ _) (inj₁ _) ()
fromto→valid {sum σ τ} (inj₂ (inj₂ b2)) (inj₂ _) (inj₂ _) ()

valid→fromto {int} v dv tt = refl
valid→fromto {pair σ τ} (a , b) (da , db) (ada , bdb) = valid→fromto a da ada , valid→fromto b db bdb
valid→fromto {σ ⇒ τ} f df fdf da a1 a2 daa = body
  where
    fa1da-valid :
      valid (f a1) (df a1 da) ×
      WellDefinedFunChangePoint f df a1 da
    fa1da-valid = fdf a1 da (fromto→valid da _ _ daa)
    body : [ τ ] df a1 da from f a1 to (f ⊕ df) a2
    body rewrite sym (fromto→⊕ da _ _ daa) | proj₂ fa1da-valid = valid→fromto (f a1) (df a1 da) (proj₁ fa1da-valid)
valid→fromto {sum σ τ} .(inj₁ a) .(inj₁ (inj₁ da)) (sv₁ a da ada) = valid→fromto a da ada
valid→fromto {sum σ τ} .(inj₂ b) .(inj₁ (inj₂ db)) (sv₂ b db bdb) = valid→fromto b db bdb
valid→fromto {sum σ τ} .(inj₁ a1) .(inj₂ (inj₂ b2)) (svrp₁ a1 b2) = refl
valid→fromto {sum σ τ} .(inj₂ b1) .(inj₂ (inj₁ a2)) (svrp₂ b1 a2) = refl
