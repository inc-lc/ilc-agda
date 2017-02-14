module New.Unused where

open import New.Changes

module _ {ℓ₁} {ℓ₂}
  {A : Set ℓ₁} {B : Set ℓ₂} {{CA : ChAlg A}} {{CB : ChAlg B}} where
  open ≡-Reasoning
  open import Postulate.Extensionality
  module _ (f : A → B) where
    nil-is-derivative : IsDerivative f (nil f)
    nil-is-derivative a da v =
      begin
        f (a ⊕ da)
      ≡⟨ sym (cong (λ □ → □ (_⊕_ a da)) (update-nil f)) ⟩
        (f ⊕ nil f) (a ⊕ da)
      ≡⟨ proj₂ (nil-valid f a da v) ⟩
        f a ⊕ (nil f a da)
      ∎

    derivative-is-nil : ∀ df → IsDerivative f df → f ⊕ df ≡ f
    derivative-is-nil df f-df =
      ext (λ v →
        begin
          f v ⊕ df v (nil v)
        ≡⟨ sym (f-df v (nil v) (nil-valid v)) ⟩
          f (v ⊕ nil v)
        ≡⟨ cong f (update-nil v) ⟩
          f v
        ∎)

    derivative-is-valid : ∀ df
      (IsDerivative-f-df : IsDerivative f df) →
      WellDefinedFunChange f df
    derivative-is-valid df IsDerivative-f-df a da ada
      rewrite sym (IsDerivative-f-df (a ⊕ da) (nil (a ⊕ da)) (nil-valid (a ⊕ da)))
      | update-nil (a ⊕ da)
      | IsDerivative-f-df a da ada
      = refl

    equal-future-expand-derivative : ∀ df → IsDerivative f df →
      ∀ v1 dv1 → valid v1 dv1 →
      ∀ v2 →
      v2 ≡ v1 ⊕ dv1 →
      f v2 ≡ f v1 ⊕ df v1 dv1
    equal-future-expand-derivative df is-derivative-f-df v1 dv1 v1dv1 v2 eq-fut =
      begin
        f v2
      ≡⟨ cong f eq-fut ⟩
        f (v1 ⊕ dv1)
      ≡⟨ is-derivative-f-df v1 dv1 v1dv1 ⟩
        f v1 ⊕ df v1 dv1
      ∎
    -- -- equal-future-expand-derivative df is-derivative-f-df v1 dv1 v1dv1 v2 dv2 v2dv2 eq-fut =
    -- --   begin
    -- --     (f ⊕ df) (v1 ⊕ dv1)
    -- --   ≡⟨ cong (f ⊕ df) eq-fut ⟩
    -- --     (f ⊕ df) (v2 ⊕ dv2)
    -- --   ≡⟨ well-defined-f-df v2 dv2 v2dv2 ⟩
    -- --     f v2 ⊕ df v2 dv2
    -- --   ∎
    --   -- equal-future-expand-base df (derivative-is-valid df is-derivative-f-df)

    equal-future-base : ∀ df → WellDefinedFunChange f df →
      ∀ v1 dv1 → valid v1 dv1 →
      ∀ v2 dv2 → valid v2 dv2 →
      v1 ⊕ dv1 ≡ v2 ⊕ dv2 →
      f v1 ⊕ df v1 dv1 ≡ f v2 ⊕ df v2 dv2
    equal-future-base df well-defined-f-df v1 dv1 v1dv1 v2 dv2 v2dv2 eq-fut =
      begin
        f v1 ⊕ df v1 dv1
      ≡⟨ sym (well-defined-f-df v1 dv1 v1dv1) ⟩
        (f ⊕ df) (v1 ⊕ dv1)
      ≡⟨ cong (f ⊕ df) eq-fut ⟩
        (f ⊕ df) (v2 ⊕ dv2)
      ≡⟨ well-defined-f-df v2 dv2 v2dv2 ⟩
        f v2 ⊕ df v2 dv2
      ∎

    equal-future-change : ∀ df → valid f df →
      ∀ v1 dv1 → valid v1 dv1 →
      ∀ v2 dv2 → valid v2 dv2 →
      v1 ⊕ dv1 ≡ v2 ⊕ dv2 →
      f v1 ⊕ df v1 dv1 ≡ f v2 ⊕ df v2 dv2
    equal-future-change df fdf =
      equal-future-base df
        (λ a da ada → proj₂ (fdf a da ada))

    equal-future-derivative : ∀ df → IsDerivative f df →
      ∀ v1 dv1 → valid v1 dv1 →
      ∀ v2 dv2 → valid v2 dv2 →
      v1 ⊕ dv1 ≡ v2 ⊕ dv2 →
      f v1 ⊕ df v1 dv1 ≡ f v2 ⊕ df v2 dv2
    equal-future-derivative df is-derivative-f-df =
      equal-future-base df (derivative-is-valid df is-derivative-f-df)
