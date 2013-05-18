module total where

-- INCREMENTAL λ-CALCULUS
--   with total derivatives
--
-- Features:
--   * changes and derivatives are unified (following Cai)
--   * Δ e describes how e changes when its free variables or its arguments change
--   * denotational semantics including semantics of changes
--
-- Work in Progress:
--   * lemmas about behavior of changes
--   * lemmas about behavior of Δ
--   * correctness proof for symbolic derivation

import Relation.Binary as B

open import Relation.Binary using
  (IsEquivalence; Setoid; Reflexive; Symmetric; Transitive)
import Relation.Binary.EqReasoning as EqR

open import Relation.Nullary using (¬_)

open import meaning
open import IlcModel
open import Changes
open import ChangeContexts
open import binding Type ⟦_⟧Type
open import TotalTerms

open import Relation.Binary.PropositionalEquality using (sym)

-- LIFTING terms into Δ-Contexts

lift-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) τ
lift-var this = that this
lift-var (that x) = that (that (lift-var x))

lift-var′ : ∀ {Γ τ} → (Γ′ : Prefix Γ) → Var Γ τ → Var (Δ-Context′ Γ Γ′) τ
lift-var′ ∅ x = lift-var x
lift-var′ (τ • Γ′) this = this
lift-var′ (τ • Γ′) (that x) = that (lift-var′ Γ′ x)

-- This version of lift-term′ uses just weakenOne to accomplish its
-- job.

lift-term′-weakenOne : ∀ {Γ τ} Γ′ →
  Term Γ τ → Term (Δ-Context′ Γ Γ′) τ
lift-term′-weakenOne {Γ} Γ′ t =
  substTerm (sym (take-⋎-Δ-Context-drop-Δ-Context′ Γ Γ′))
    (doWeakenMore (take Γ Γ′) (drop Γ Γ′)
      (substTerm (sym (take-drop Γ Γ′))
        t))
  where
    doWeakenMore : ∀ Γprefix Γrest {τ} →
      Term (Γprefix ⋎ Γrest) τ →
      Term (Γprefix ⋎ Δ-Context Γrest) τ

    doWeakenMore Γprefix ∅ t₁ = t₁
    doWeakenMore Γprefix (τ₂ • Γrest) t₁ =
      weakenOne Γprefix (Δ-Type τ₂)
        (substTerm (sym (move-prefix Γprefix τ₂ (Δ-Context Γrest)))
          (doWeakenMore (Γprefix ⋎ (τ₂ • ∅)) Γrest
            (substTerm (move-prefix Γprefix τ₂ Γrest) t₁)))

lift-term′ : ∀ {Γ τ} → (Γ′ : Prefix Γ) → Term Γ τ → Term (Δ-Context′ Γ Γ′) τ
lift-term′ Γ′ (abs t) = abs (lift-term′ (_ • Γ′) t)
lift-term′ Γ′ (app t₁ t₂) = app (lift-term′ Γ′ t₁) (lift-term′ Γ′ t₂)
lift-term′ Γ′ (var x) = var (lift-var′ Γ′ x)
lift-term′ Γ′ true = true
lift-term′ Γ′ false = false
lift-term′ Γ′ (if t₁ t₂ t₃) = if (lift-term′ Γ′ t₁) (lift-term′ Γ′ t₂) (lift-term′ Γ′ t₃)
lift-term′ Γ′ (Δ t) = lift-term′-weakenOne Γ′ (Δ t)
lift-term′ {τ = τ} Γ′ (weakenOne Γ₁ τ₂ {Γ₃} t) = lift-weakened-term Γ₁ τ₂ Γ′ t
  where
    double-weakenOne :
      ∀ Γ₁ {Γ₃ τ} τ₂ → Term (Γ₁ ⋎ Γ₃) τ → 
      Term (Δ-Context (Γ₁ ⋎ (τ₂ • Γ₃))) τ
    double-weakenOne Γ₁ {Γ₃} τ₂ t =
      substTerm (Δ-Context-⋎-expanded Γ₁ τ₂ Γ₃)
        (weakenOne (Δ-Context Γ₁) _
          (weakenOne (Δ-Context Γ₁) _
            (substTerm (Δ-Context-⋎ Γ₁ Γ₃) (lift-term′ ∅ t))))

    lift-weakened-term :
      ∀ Γ₁ {Γ₃ τ} τ₂ Γ′ → Term (Γ₁ ⋎ Γ₃) τ → 
      Term (Δ-Context′ (Γ₁ ⋎ (τ₂ • Γ₃)) Γ′) τ
    lift-weakened-term ∅ τ₂ ∅ t = double-weakenOne ∅ τ₂ t
    lift-weakened-term Γ₁ τ₂ ∅ t = double-weakenOne Γ₁ τ₂ t
    lift-weakened-term ∅ τ₃ (.τ₃ • Γ′₁) t₁ = weakenOne ∅ τ₃ (lift-term′ Γ′₁ t₁)
    lift-weakened-term (τ₁ • Γ₁) {Γ₃} τ₂ (.τ₁ • Γ′₁) t₁ =
      lift-term′-weakenOne (τ₁ • Γ′₁) (weakenOne (τ₁ • Γ₁) τ₂ t₁)

lift-term : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) τ
lift-term = lift-term′ ∅

-- PROPERTIES of lift-term

lift-var-ignore : ∀ {Γ τ} (ρ : ⟦ Δ-Context Γ ⟧) (x : Var Γ τ) →
  ⟦ lift-var x ⟧ ρ ≡ ⟦ x ⟧ (ignore ρ)
lift-var-ignore (v • dv • ρ) this = ≡-refl
lift-var-ignore (v • dv • ρ) (that x) = lift-var-ignore ρ x

lift-var-ignore′ : ∀ {Γ τ} →
  (Γ′ : Prefix Γ) (ρ : ⟦ Δ-Context′ Γ Γ′ ⟧) (x : Var Γ τ) →
  ⟦ lift-var′ Γ′ x ⟧ ρ ≡ ⟦ x ⟧ (ignore′ Γ′ ρ)
lift-var-ignore′ ∅ ρ x = lift-var-ignore ρ x
lift-var-ignore′ (τ • Γ′) (v • ρ) this = ≡-refl
lift-var-ignore′ (τ • Γ′) (v • ρ) (that x) = lift-var-ignore′ Γ′ ρ x

lift-term-ignore′ : ∀ {Γ τ} →
  (Γ′ : Prefix Γ) {ρ : ⟦ Δ-Context′  Γ Γ′ ⟧} (t : Term Γ τ) →
  ⟦ lift-term′ Γ′ t ⟧ ρ ≡ ⟦ t ⟧ (ignore′ Γ′ ρ)
lift-term-ignore′ Γ′ (abs t) =
  ext (λ v → lift-term-ignore′ (_ • Γ′) t)
lift-term-ignore′ Γ′ (app t₁ t₂) =
  ≡-app (lift-term-ignore′ Γ′ t₁) (lift-term-ignore′ Γ′ t₂)
lift-term-ignore′ Γ′ (var x) = lift-var-ignore′ Γ′ _ x
lift-term-ignore′ Γ′ true = ≡-refl
lift-term-ignore′ Γ′ false = ≡-refl
lift-term-ignore′ Γ′ {ρ} (if t₁ t₂ t₃)
  with ⟦ lift-term′ Γ′ t₁ ⟧ ρ
     | ⟦ t₁ ⟧ (ignore′ Γ′ ρ)
     | lift-term-ignore′ Γ′ {ρ} t₁
... | true | true | bool = lift-term-ignore′ Γ′ t₂
... | false | false | bool = lift-term-ignore′ Γ′ t₃
lift-term-ignore′ Γ′ (Δ t) = {!!}
lift-term-ignore′ _ (weakenOne _ _ {_} {._} _) = {!!}

lift-term-ignore : ∀ {Γ τ} {ρ : ⟦ Δ-Context Γ ⟧} (t : Term Γ τ) →
  ⟦ lift-term t ⟧ ρ ≡ ⟦ t ⟧ (ignore ρ)
lift-term-ignore = lift-term-ignore′ ∅


-- PROPERTIES of Δ

Δ-abs : ∀ {Γ τ₁ τ₂} (t : Term (τ₁ • Γ) τ₂) →
  Δ (abs t) ≈ abs (abs (Δ t))
Δ-abs t = ext (λ ρ → ≡-refl)

Δ-app : ∀ {Γ τ₁ τ₂} (t₁ : Term Γ (τ₁ ⇒ τ₂)) (t₂ : Term Γ τ₁) →
  Δ (app t₁ t₂) ≈ app (app (Δ t₁) (lift-term t₂)) (Δ t₂)
Δ-app t₁ t₂ = ≈-sym (ext (λ ρ →
  begin
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ lift-term t₂ ⟧ ρ)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ lift-term t₂ ⟧ ρ))
  ≡⟨ ≡-cong
       (λ x →
          diff
          (⟦ t₁ ⟧ (update ρ)
           (apply (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) x))
          (⟦ t₁ ⟧ (ignore ρ) x))
       (lift-term-ignore {ρ = ρ} t₂) ⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ t₂ ⟧ (ignore ρ))))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ≡⟨  ≡-cong
       (λ x →
          diff (⟦ t₁ ⟧ (update ρ) x) (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ))))
       (apply-diff (⟦ t₂ ⟧ (ignore ρ)) (⟦ t₂ ⟧ (update ρ)))  ⟩
    diff
      (⟦ t₁ ⟧ (update ρ) (⟦ t₂ ⟧ (update ρ)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ t₂ ⟧ (ignore ρ)))
  ∎)) where open ≡-Reasoning

-- SYMBOLIC DERIVATION

derive-var : ∀ {Γ τ} → Var Γ τ → Var (Δ-Context Γ) (Δ-Type τ)
derive-var this = this
derive-var (that x) = that (that (derive-var x))

diff-term : ∀ {Γ τ} → Term Γ τ → Term Γ τ → Term Γ (Δ-Type τ)
diff-term = {!!}

apply-term : ∀ {Γ τ} → Term Γ (Δ-Type τ) → Term Γ τ → Term Γ τ
apply-term = {!!}

_and_ : ∀ {Γ} → Term Γ bool → Term Γ bool → Term Γ bool
a and b = {!!}

!_ : ∀ {Γ} → Term Γ bool → Term Γ bool
! x = {!!}

derive-term : ∀ {Γ τ} → Term Γ τ → Term (Δ-Context Γ) (Δ-Type τ)
derive-term (abs t) = abs (abs (derive-term t))
derive-term (app t₁ t₂) = app (app (derive-term t₁) (lift-term t₂)) (derive-term t₂)
derive-term (var x) = var (derive-var x)
derive-term true = false
derive-term false = false
derive-term (if c t e) =
  if ((derive-term c) and (lift-term c))
    (diff-term (apply-term (derive-term e) (lift-term e)) (lift-term t))
    (if ((derive-term c) and (lift-term (! c)))
      (diff-term (apply-term (derive-term t) (lift-term t)) (lift-term e))
      (if (lift-term c)
        (derive-term t)
        (derive-term e)))

derive-term (Δ t) = Δ (derive-term t)
derive-term (weakenOne Γ₁ τ₂ {Γ₃} t) =
  substTerm (Δ-Context-⋎-expanded Γ₁ τ₂ Γ₃)
    (weakenOne (Δ-Context Γ₁) (Δ-Type τ₂)
      (weakenOne (Δ-Context Γ₁) τ₂
        (substTerm (Δ-Context-⋎ Γ₁ Γ₃)
          (derive-term t))))

-- CORRECTNESS of derivation

derive-var-correct : ∀ {Γ τ} → (ρ : ⟦ Δ-Context Γ ⟧) → (x : Var Γ τ) →
  diff (⟦ x ⟧ (update ρ)) (⟦ x ⟧ (ignore ρ)) ≡
  ⟦ derive-var x ⟧ ρ
derive-var-correct (dv • v • ρ) this = diff-apply dv v
derive-var-correct (dv • v • ρ) (that x) = derive-var-correct ρ x

derive-term-correct : ∀ {Γ τ} → (t : Term Γ τ) →
   Δ t ≈ derive-term t
derive-term-correct {Γ} (abs t) =
  begin
    Δ (abs t)
  ≈⟨ Δ-abs t ⟩
    abs (abs (Δ t))
  ≈⟨ ≈-abs (≈-abs (derive-term-correct t)) ⟩
    abs (abs (derive-term t))
  ≈⟨ ≈-refl ⟩
    derive-term (abs t)
  ∎ where open ≈-Reasoning
derive-term-correct (app t₁ t₂) =
  begin
    Δ (app t₁ t₂)
  ≈⟨ Δ-app t₁ t₂ ⟩
    app (app (Δ t₁) (lift-term t₂)) (Δ t₂)
  ≈⟨ ≈-app (≈-app (derive-term-correct t₁) ≈-refl) (derive-term-correct t₂) ⟩
    app (app (derive-term t₁) (lift-term t₂)) (derive-term t₂)
  ≈⟨ ≈-refl ⟩
    derive-term (app t₁ t₂)
  ∎ where open ≈-Reasoning
derive-term-correct (var x) = ext (λ ρ → derive-var-correct ρ x)
derive-term-correct true = ext (λ ρ → ≡-refl)
derive-term-correct false = ext (λ ρ → ≡-refl)
derive-term-correct (if t₁ t₂ t₃) = {!!}
derive-term-correct (Δ t) = ≈-Δ (derive-term-correct t)
derive-term-correct (weakenOne _ _ t) = {!!}
