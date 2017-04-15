module Thesis.RelateToValidity where

open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Thesis.Changes
open import Thesis.Lang

module _
  {A : Set} {B : Set} {{CA : ChangeStructure A}} {{CB : ChangeStructure B}} where

  WellDefinedFunChangePoint : ∀ (f : A → B) → (df : Ch (A → B)) → ∀ a da → Set
  WellDefinedFunChangePoint f df a da = (f ⊕ df) (a ⊕ da) ≡ f a ⊕ df a da

  WellDefinedFunChangeFromTo′ : ∀ (f1 : A → B) → (df : Ch (A → B)) → Set
  WellDefinedFunChangeFromTo′ f1 df = ∀ da a → ch da from a to (a ⊕ da) → WellDefinedFunChangePoint f1 df a da

  open ≡-Reasoning

  fromto→WellDefined′ : ∀ {f1 f2 df} → ch df from f1 to f2 →
    WellDefinedFunChangeFromTo′ f1 df
  fromto→WellDefined′ {f1 = f1} {f2} {df} dff da a daa =
    begin
      (f1 ⊕ df) (a ⊕ da)
    ≡⟨ cong (λ □ → □ (a ⊕ da)) (fromto→⊕ df f1 f2 dff)⟩
      f2 (a ⊕ da)
    ≡⟨ sym (fromto→⊕ _ _ _ (dff da _ _ daa)) ⟩
      f1 a ⊕ df a da
    ∎

  -- This is similar (not equivalent) to the old definition of function changes.
  -- However, such a function need not be defined on invalid changes, unlike the
  -- functions.
  --
  -- Hence this is sort of bigger than Δ f, though not really.
  fΔ : (A → B) → Set
  fΔ f = (a : A) → Δ a → Δ (f a)

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
  valid-functions-map-Δ : ∀ (f : A → B) (df : Δ f) → fΔ f
  valid-functions-map-Δ f (df , dff) a (da , daa) = df a da , valid-res
    where
      valid-res : ch df a da from f a to (f a ⊕ df a da)
      valid-res rewrite sym (fromto→WellDefined′ dff da a daa) = dff da a (a ⊕ da) daa

  fromto-functions-map-Δ : ∀ (f1 f2 : A → B) (df : Ch (A → B)) → ch df from f1 to f2 → fΔ f1
  fromto-functions-map-Δ f1 f2 df dff a (da , daa) = valid-functions-map-Δ f1 (df , dff′) a (da , daa)
    where
      dff′ : ch df from f1 to (f1 ⊕ df)
      dff′ = subst (ch df from f1 to_) (sym (fromto→⊕ df f1 f2 dff)) dff

open import Thesis.LangChanges

fromto→WellDefined′Lang : ∀ {σ τ f1 f2 df} → [ σ ⇒ τ ]τ df from f1 to f2 →
  WellDefinedFunChangeFromTo′ f1 df
fromto→WellDefined′Lang {f1 = f1} {f2} {df} dff da a daa =
  fromto→WellDefined′ dff da a daa
