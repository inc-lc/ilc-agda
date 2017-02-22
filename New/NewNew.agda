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

-- XXX This would be more elegant as a datatype — that would avoid the need for
-- an equality proof.
[_]Γ_from_to_ : ∀ Γ → eCh Γ → (ρ1 ρ2 : ⟦ Γ ⟧Context) → Set
[ ∅ ]Γ ∅ from ∅ to ∅ = ⊤
[ τ • Γ ]Γ (dv • v1' • dρ) from (v1 • ρ1) to (v2 • ρ2) =
   [ τ ] dv from v1 to v2 × v1 ≡ v1' × [ Γ ]Γ dρ from ρ1 to ρ2

⟦Γ≼ΔΓ⟧ : ∀ {Γ ρ1 ρ2 dρ} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ρ1 ≡ ⟦ Γ≼ΔΓ ⟧≼ dρ
⟦Γ≼ΔΓ⟧ {∅} {∅} {∅} {∅} tt = refl
⟦Γ≼ΔΓ⟧ {_ • _} {v1 • ρ1} {v2 • ρ2} {dv • .v1 • dρ} (dvv , refl , dρρ) = cong₂ _•_ refl (⟦Γ≼ΔΓ⟧ dρρ)

fit-sound : ∀ {Γ τ} → (t : Term Γ τ) →
  ∀ {ρ1 ρ2 dρ} → [ Γ ]Γ dρ from ρ1 to ρ2 →
  ⟦ t ⟧Term ρ1 ≡ ⟦ fit t ⟧Term dρ
fit-sound t dρρ = trans
  (cong ⟦ t ⟧Term (⟦Γ≼ΔΓ⟧ dρρ))
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
fromtoDerive τ (app {σ} s t) dρρ rewrite sym (fit-sound t dρρ) =
  let fromToF = fromtoDerive (σ ⇒ τ) s dρρ
  in let fromToB = fromtoDerive σ t dρρ in fromToF _ _ _ fromToB
fromtoDerive (σ ⇒ τ) (abs t) dρρ = λ da a1 a2 daa →
  fromtoDerive τ t (daa , refl , dρρ)

-- Now relate this validity with ⊕. To know that nil and so on are valid, also
-- relate it to the other definition.
open import Postulate.Extensionality

fromto→⊕ : ∀ {τ} dv v1 v2 →
  [ τ ] dv from v1 to v2 →
  v1 ⊕ dv ≡ v2

⊝-fromto : ∀ {τ} (v1 v2 : ⟦ τ ⟧Type) → [ τ ] v2 ⊝ v1 from v1 to v2
⊝-fromto {σ ⇒ τ} f1 f2 da a1 a2 daa rewrite sym (fromto→⊕ _ _ _ daa) = ⊝-fromto (f1 a1) (f2 (a1 ⊕ da))
⊝-fromto {int} v1 v2 = sym (update-diff v2 v1)
⊝-fromto {pair σ τ} (a1 , b1) (a2 , b2) = ⊝-fromto a1 a2 , ⊝-fromto b1 b2

nil-fromto : ∀ {τ} (v : ⟦ τ ⟧Type) → [ τ ] nil v from v to v
nil-fromto v = ⊝-fromto v v

fromto→⊕ {σ ⇒ τ} df f1 f2 dff =
  ext (λ v → fromto→⊕ {τ} (df v (nil v)) (f1 v) (f2 v) (dff (nil v) v v (nil-fromto v)))
fromto→⊕ {int} dn n1 n2 refl = refl
fromto→⊕ {pair σ τ} (da , db) (a1 , b1) (a2 , b2) (daa , dbb) =
  cong₂ _,_ (fromto→⊕ _ _ _ daa) (fromto→⊕ _ _ _ dbb)

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
    daa′ rewrite fromto→⊕ da a1 a2 daa = daa

-- Recursive isomorphism between the two validities.
--
-- Among other things, valid→fromto proves that a validity-preserving function,
-- with validity defined via (f1 ⊕ df) (a ⊕ da) ≡ f1 a ⊕ df a da, is also valid
-- in the "fromto" sense.
--
-- We can't hope for a better statement, since we need the equation to be
-- satisfied also by returned or argument functions.

fromto→valid : ∀ {τ} →
  ∀ v1 v2 dv → [ τ ] dv from v1 to v2 →
  valid v1 dv
valid→fromto : ∀ {τ} v (dv : Cht τ) → valid v dv → [ τ ] dv from v to (v ⊕ dv)

fromto→valid {int} = λ v1 v2 dv x → tt
fromto→valid {pair σ τ} (a1 , b1) (a2 , b2) (da , db) (daa , dbb) = (fromto→valid  _ _ _ daa) , (fromto→valid _ _ _ dbb)
fromto→valid {σ ⇒ τ} f1 f2 df dff = λ a da ada →
  fromto→valid _ _ _ (dff da a (a ⊕ da) (valid→fromto a da ada)) ,
  fromto→WellDefined′ dff da a (valid→fromto _ _ ada)

valid→fromto {int} v dv tt = refl
valid→fromto {pair σ τ} (a , b) (da , db) (ada , bdb) = valid→fromto a da ada , valid→fromto b db bdb
valid→fromto {σ ⇒ τ} f df fdf da a1 a2 daa = body
  where
    fa1da-valid :
      valid (f a1) (df a1 da) ×
      WellDefinedFunChangePoint f df a1 da
    fa1da-valid = fdf a1 da (fromto→valid _ _ _ daa)
    body : [ τ ] df a1 da from f a1 to (f ⊕ df) a2
    body rewrite sym (fromto→⊕ _ _ _ daa) | proj₂ fa1da-valid = valid→fromto (f a1) (df a1 da) (proj₁ fa1da-valid)
