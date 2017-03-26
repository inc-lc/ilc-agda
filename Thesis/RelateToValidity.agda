module Thesis.RelateToValidity where

open import Relation.Binary.PropositionalEquality public hiding ([_])

open import Thesis.Changes
open import Thesis.Lang

module _
  {A : Set} {B : Set} {{CA : ChangeStructure A}} {{CB : ChangeStructure B}} where

  WellDefinedFunChangePoint : ∀ (f : A → B) → (df : Ch (A → B)) → ∀ a da → Set
  WellDefinedFunChangePoint f df a da = (f ⊕ df) (a ⊕ da) ≡ f a ⊕ df a da

open import Thesis.LangChanges

WellDefinedFunChangeFromTo′ : ∀ {σ τ} (f1 : ⟦ σ ⇒ τ ⟧Type) → (df : Chτ (σ ⇒ τ)) → Set
WellDefinedFunChangeFromTo′ f1 df = ∀ da a → [ _ ]τ da from a to (a ⊕ da) → WellDefinedFunChangePoint f1 df a da

open ≡-Reasoning

fromto→WellDefined′ : ∀ {σ τ f1 f2 df} → [ σ ⇒ τ ]τ df from f1 to f2 →
  WellDefinedFunChangeFromTo′ f1 df
fromto→WellDefined′ {f1 = f1} {f2} {df} dff da a daa =
  begin
    (f1 ⊕ df) (a ⊕ da)
  ≡⟨ cong (λ □ → □ (a ⊕ da)) (fromto→⊕ df f1 f2 dff)⟩
    f2 (a ⊕ da)
  ≡⟨ sym (fromto→⊕ _ _ _ (dff da _ _ daa)) ⟩
    f1 a ⊕ df a da
  ∎

-- TODO: prove the converse of the above statement. Which is a bit harder, since
-- you first need to state it.
