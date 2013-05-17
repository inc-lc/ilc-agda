module Changes where

open import meaning
open import IlcModel

-- CHANGE TYPES

Δ-Type : Type → Type
Δ-Type (τ₁ ⇒ τ₂) = τ₁ ⇒ Δ-Type τ₁ ⇒ Δ-Type τ₂
Δ-Type (bool) = bool -- true means negate, false means nil change

derive : ∀ {τ} → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧
apply : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ τ ⟧ → ⟦ τ ⟧
diff : ∀ {τ} → ⟦ τ ⟧ → ⟦ τ ⟧ → ⟦ Δ-Type τ ⟧

diff {τ₁ ⇒ τ₂} f₁ f₂ = λ v dv → diff (f₁ (apply dv v)) (f₂ v)
diff {bool} true true = false
diff {bool} true false = true
diff {bool} false true = true
diff {bool} false false = false

derive {τ₁ ⇒ τ₂} f = λ v dv → diff (f (apply dv v)) (f v)
derive {bool} b = false

apply {τ₁ ⇒ τ₂} df f = λ v → apply (df v (derive v)) (f v)
apply {bool} true true = false
apply {bool} true false = true
apply {bool} false true = true
apply {bool} false false = false

compose : ∀ {τ} → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧ → ⟦ Δ-Type τ ⟧
compose {τ₁ ⇒ τ₂} df₁ df₂ = λ v dv → compose (df₁ v dv) (df₂ v dv)
compose {bool} true true = false
compose {bool} true false = true
compose {bool} false true = true
compose {bool} false false = false

-- CONGRUENCE rules for change operations

≡-diff : ∀ {τ : Type} {v₁ v₂ v₃ v₄ : ⟦ τ ⟧} →
  v₁ ≡ v₂ → v₃ ≡ v₄ → diff v₁ v₃ ≡ diff v₂ v₄
≡-diff = ≡-cong₂ diff

≡-apply : ∀ {τ : Type} {dv₁ dv₂ : ⟦ Δ-Type τ ⟧} {v₁ v₂ : ⟦ τ ⟧} →
  dv₁ ≡ dv₂ → v₁ ≡ v₂ → apply dv₁ v₁ ≡ apply dv₂ v₂
≡-apply = ≡-cong₂ apply

-- PROPERTIES of changes

diff-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  diff v v ≡ derive v
diff-derive {τ₁ ⇒ τ₂} v = ≡-refl
diff-derive {bool} true = bool
diff-derive {bool} false = bool

-- XXX: as given, this is false!
postulate
  diff-apply : ∀ {τ} (dv : ⟦ Δ-Type τ ⟧) (v : ⟦ τ ⟧) →
    diff (apply dv v) v ≡ dv

{-
diff-apply {τ₁ ⇒ τ₂} df f = ext (λ v → ext (λ dv →
  {!!}))
diff-apply {bool} true true = bool
diff-apply {bool} true false = bool
diff-apply {bool} false true = bool
diff-apply {bool} false false = bool
-}

apply-diff : ∀ {τ} (v₁ v₂ : ⟦ τ ⟧) →
  apply (diff v₂ v₁) v₁ ≡ v₂

apply-derive : ∀ {τ} (v : ⟦ τ ⟧) →
  apply (derive v) v ≡ v

apply-diff {τ₁ ⇒ τ₂} f₁ f₂ = ext (λ v →
  begin
    apply (diff f₂ f₁) f₁ v
  ≡⟨ ≡-refl ⟩
    apply (diff (f₂ (apply (derive v) v)) (f₁ v)) (f₁ v)
  ≡⟨ ≡-apply (≡-diff (≡-cong f₂ (apply-derive v)) ≡-refl) ≡-refl ⟩
    apply (diff (f₂ v) (f₁ v)) (f₁ v)
  ≡⟨ apply-diff (f₁ v) (f₂ v) ⟩
    f₂ v
  ∎) where open ≡-Reasoning
apply-diff {bool} true true = bool
apply-diff {bool} true false = bool
apply-diff {bool} false true = bool
apply-diff {bool} false false = bool

apply-derive {τ₁ ⇒ τ₂} f = ext (λ v →
  begin
    apply (derive f) f v
  ≡⟨ ≡-refl ⟩
    apply (diff (f (apply (derive v) v)) (f v)) (f v)
  ≡⟨ ≡-cong (λ x → apply (diff (f x) (f v)) (f v)) (apply-derive v) ⟩
    apply (diff (f v) (f v)) (f v)
  ≡⟨ apply-diff (f v) (f v)⟩
    f v
  ∎) where open ≡-Reasoning
apply-derive {bool} true = bool
apply-derive {bool} false = bool

apply-compose : ∀ {τ} (v : ⟦ τ ⟧) (dv₁ dv₂ : ⟦ Δ-Type τ ⟧) →
  apply (compose dv₁ dv₂) v ≡ apply dv₁ (apply dv₂ v)
apply-compose {τ₁ ⇒ τ₂} f df₁ df₂ = ext (λ v →
  apply-compose (f v) (df₁ v (derive v)) (df₂ v (derive v)))
apply-compose {bool} true true true = bool
apply-compose {bool} true true false = bool
apply-compose {bool} true false true = bool
apply-compose {bool} true false false = bool
apply-compose {bool} false true true = bool
apply-compose {bool} false true false = bool
apply-compose {bool} false false true = bool
apply-compose {bool} false false false = bool

compose-assoc : ∀ {τ} (dv₁ dv₂ dv₃ : ⟦ Δ-Type τ ⟧) →
  compose dv₁ (compose dv₂ dv₃) ≡ compose (compose dv₁ dv₂) dv₃
compose-assoc {τ₁ ⇒ τ₂} df₁ df₂ df₃ = ext (λ v → ext (λ dv →
  compose-assoc (df₁ v dv) (df₂ v dv) (df₃ v dv)))
compose-assoc {bool} true true true = bool
compose-assoc {bool} true true false = bool
compose-assoc {bool} true false true = bool
compose-assoc {bool} true false false = bool
compose-assoc {bool} false true true = bool
compose-assoc {bool} false true false = bool
compose-assoc {bool} false false true = bool
compose-assoc {bool} false false false = bool
