module Thesis.RelateToValidity where

open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Thesis.Changes
open import Thesis.Lang

module _ {A : Set} {{CA : ChangeStructure A}} where
  fromto→valid fromto→valid-2 : ∀ da (a1 a2 : A) (daa : ch da from a1 to a2) → valid a1 da
  fromto→valid da a1 a2 daa rewrite fromto→⊕ da a1 _ daa = daa
  fromto→valid-2 da a1 a2 daa = subst (ch da from a1 to_) (sym (fromto→⊕ da a1 a2 daa)) daa

  -- The "inverse" is so trivial to not be worth calling, hence commented out:
  -- valid→fromto : ∀ da (a : A) → (valid a da) → ch da from a to (a ⊕ da)
  -- valid→fromto _ _ daa = daa

module _
  {A : Set} {B : Set} {{CA : ChangeStructure A}} {{CB : ChangeStructure B}} where

  WellDefinedFunChangePoint : ∀ (f : A → B) → (df : Ch (A → B)) → ∀ a da → Set
  WellDefinedFunChangePoint f df a da = (f ⊕ df) (a ⊕ da) ≡ f a ⊕ df a da

  WellDefinedFunChangeFromTo′ : ∀ (f1 : A → B) → (df : Ch (A → B)) → Set
  WellDefinedFunChangeFromTo′ f1 df = ∀ da a → valid a da → WellDefinedFunChangePoint f1 df a da

  open ≡-Reasoning
  open import Function

  fromto-incrementalization : ∀ {f1 f2 : A → B} {df} → ch df from f1 to f2 →
    ∀ {da a} → valid a da →
    f1 a ⊕ df a da ≡ f2 (a ⊕ da)
  fromto-incrementalization {f1 = f1} {f2} {df} dff {da} {a} daa = fromto→⊕ _ _ _ (dff da a _ daa)

  fromto→valid-fun : ∀ {f1 f2 : A → B} {df : Ch (A → B)} → ch df from f1 to f2 → ∀ {a da} (daa : valid a da) → valid (f1 a) (df a da)
  fromto→valid-fun {f1} {f2} {df} dff {a} {da} daa = fromto→valid (df a da) (f1 a) _ (dff da a _ daa)

  fromto→WellDefined′ : ∀ {f1 f2 df} → ch df from f1 to f2 →
    WellDefinedFunChangeFromTo′ f1 df
  fromto→WellDefined′ {f1 = f1} {f2} {df} dff da a daa =
    begin
      (f1 ⊕ df) (a ⊕ da)
    ≡⟨ cong (_$ (a ⊕ da)) (fromto→⊕ df f1 f2 dff)⟩
      f2 (a ⊕ da)
    ≡⟨ sym (fromto-incrementalization dff daa) ⟩
      f1 a ⊕ df a da
    ∎

  -- Δ f is similar to function changes in PLDI'14, but PLDI'14 function changes
  -- need not be defined on invalid changes; instead, if (df, dff) : Δ f, then
  -- df is a function change that is also defined on invalid changes.
  --
  -- Next we define fΔ. It is closer to the PLDI'14 definition of function
  -- changes; but it is not defined recursively, so it still produces new-style
  -- function changes.
  --
  -- Hence this is sort of bigger than Δ f, though not really.
  fΔ : (A → B) → Set
  fΔ f = (a : A) → Δ₁ a → Δ₁ (f a)

  -- We can indeed map Δ f into fΔ f, via valid-functions-map-Δ. If this mapping
  -- were an injection, we could say that fΔ f is bigger than Δ f. But we'd need
  -- first to quotient Δ f to turn valid-functions-map-Δ into an injection:
  --
  -- 1. We need to quotient Δ f by extensional equivalence of functions.
  --    Luckily, we can just postulate it.
  --
  -- 2. We need to quotient Δ f by identifying functions that only differ by
  --    behavior on invalid changes; such functions can't be distinguished after
  --    being injected into fΔ f.
  valid-functions-map-Δ : ∀ (f : A → B) (df : Δ₁ f) → fΔ f
  valid-functions-map-Δ f (df , dff) a (da , daa) = df a da , valid-res
    where
      valid-res : ch df a da from f a to (f a ⊕ df a da)
      valid-res rewrite sym (fromto→WellDefined′ dff da a daa) = dff da a (a ⊕ da) daa

  -- Two alternative proofs
  fromto-functions-map-Δ-1 fromto-functions-map-Δ-2 : ∀ (f1 f2 : A → B) (df : Ch (A → B)) → ch df from f1 to f2 → fΔ f1
  fromto-functions-map-Δ-1 f1 f2 df dff a (da , daa) = valid-functions-map-Δ f1 (df , fromto→valid df f1 f2 dff) a (da , daa)

  fromto-functions-map-Δ-2 f1 f2 df dff a (da , daa) = df a da , fromto→valid-fun dff daa

open import Thesis.LangChanges

fromto→WellDefined′Lang : ∀ {σ τ f1 f2 df} → [ σ ⇒ τ ]τ df from f1 to f2 →
  WellDefinedFunChangeFromTo′ f1 df
fromto→WellDefined′Lang {f1 = f1} {f2} {df} dff da a daa =
  fromto→WellDefined′ dff da a daa
