module Denotational.Evaluation.Total where

-- EVALUATION with a primitive for TOTAL DERIVATIVES
--
-- This module defines the semantics of terms that support a
-- primitive (Δ e) for computing the total derivative according
-- to all free variables in e and all future arguments of e if e
-- is a function.

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total
open import Syntactic.Changes

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type

open import Changes
open import ChangeContexts

-- TERMS

-- Denotational Semantics

⟦_⟧Term : ∀ {Γ τ} → Term Γ τ → ⟦ Γ ⟧ → ⟦ τ ⟧
⟦ abs t ⟧Term ρ = λ v → ⟦ t ⟧Term (v • ρ)
⟦ app t₁ t₂ ⟧Term ρ = (⟦ t₁ ⟧Term ρ) (⟦ t₂ ⟧Term ρ)
⟦ var x ⟧Term ρ = ⟦ x ⟧ ρ
⟦ true ⟧Term ρ = true
⟦ false ⟧Term ρ = false
⟦ if t₁ t₂ t₃ ⟧Term ρ = if ⟦ t₁ ⟧Term ρ then ⟦ t₂ ⟧Term ρ else ⟦ t₃ ⟧Term ρ
⟦ Δ Γ′ t ⟧Term ρ = diff (⟦ t ⟧Term (update (⟦ Γ′ ⟧ ρ))) (⟦ t ⟧Term (ignore (⟦ Γ′ ⟧ ρ)))

{-

Here is an example to understand the semantics of Δ. I will use a
named variable representation for the task.

Consider the typing judgment:

   x: T |- x: T

Thus, we have that:

   dx : Δ T, x: T |- Δ x : Δ T

Thanks to weakening, we also have:

   y : S, dx : Δ T, x: T |- Δ x : Δ T

In the formalization, we need a proof Γ′ that the context Γ₁ = dx : Δ
T, x: T is a subcontext of Γ₂ = y : S, dx : Δ T, x: T. Thus, Γ′ has
type Γ₁ ≼ Γ₂.

Now take the environment:

   ρ = y ↦ w, dx ↦ dv, x ↦ v

Since the semantics of Γ′ : Γ₁ ≼ Γ₂ is a function from environments
for Γ₂ to environments for Γ₁, we have that:

   ⟦ Γ′ ⟧ ρ = dx ↦ dv, x ↦ v

From the definitions of update and ignore, it follows that:

   update (⟦ Γ′ ⟧ ρ) =  x ↦ dv ⊕ v
   ignore (⟦ Γ′ ⟧ ρ) =  x ↦ v

Hence, finally, we have that:

   diff (⟦ t ⟧Term (update (⟦ Γ′ ⟧ ρ))) (⟦ t ⟧Term (ignore (⟦ Γ′ ⟧ ρ)))

is simply diff (dv ⊕ v) v (or (dv ⊕ v) ⊝ v). If dv is a valid change,
that's just dv, that is ⟦ dx ⟧ ρ. In other words, if dv is a valid
change then ⟦ Δ Γ′ x ⟧ ρ ≡ ⟦ dx ⟧ ρ ≡ ⟦ derive-term x ⟧ ρ. This
fact, generalized for arbitrary terms, is proven formally by
derive-term-correct.

-}


meaningOfTerm : ∀ {Γ τ} → Meaning (Term Γ τ)
meaningOfTerm = meaning ⟦_⟧Term

-- PROPERTIES of WEAKENING

weaken-sound : ∀ {Γ₁ Γ₂ τ} (t : Term Γ₁ τ) {Γ′ : Γ₁ ≼ Γ₂} →
  ∀ (ρ : ⟦ Γ₂ ⟧) → ⟦ weaken Γ′ t ⟧ ρ ≡ ⟦ t ⟧ (⟦ Γ′ ⟧ ρ)
weaken-sound (abs t) ρ = ext (λ v → weaken-sound t (v • ρ))
weaken-sound (app t₁ t₂) ρ = ≡-app (weaken-sound t₁ ρ) (weaken-sound t₂ ρ)
weaken-sound (var x) ρ = lift-sound _ x ρ
weaken-sound true ρ = refl
weaken-sound false ρ = refl
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ with weaken-sound t₁ {Γ′} ρ
... | H with ⟦ weaken Γ′ t₁ ⟧ ρ | ⟦ t₁ ⟧ (⟦ Γ′ ⟧ ρ)
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ | refl | true | true = weaken-sound t₂ {Γ′} ρ
weaken-sound (if t₁ t₂ t₃) {Γ′} ρ | refl | false | false = weaken-sound t₃ {Γ′} ρ
weaken-sound (Δ Γ′ t) {Γ″} ρ =
  cong (λ x → diff (⟦ t ⟧ (update x)) (⟦ t ⟧ (ignore x))) (⟦⟧-≼-trans Γ′ Γ″ ρ)

-- Simplification rules for weakening

≡-weaken⁰ : ∀ {Γ τ} (t : Term Γ τ) →
  ∀ (ρ : ⟦ Γ ⟧) → ⟦ weaken⁰ t ⟧ ρ ≡ ⟦ t ⟧ ρ
≡-weaken⁰ t ρ =
  begin
    ⟦ weaken⁰ t ⟧ ρ
  ≡⟨ weaken-sound t ρ ⟩
    ⟦ t ⟧ (⟦ ≼-refl ⟧ ρ)
  ≡⟨ cong ⟦ t ⟧ (⟦⟧-≼-refl ρ) ⟩
    ⟦ t ⟧ ρ
  ∎ where open ≡-Reasoning

≡-weaken¹ : ∀ {Γ τ} {τ₁ : Type} (t : Term Γ τ) →
  ∀ (v₁ : ⟦ τ₁ ⟧) (ρ : ⟦ Γ ⟧) → ⟦ weaken¹ t ⟧ (v₁ • ρ) ≡ ⟦ t ⟧ ρ
≡-weaken¹ t v₁ ρ =
  begin
    ⟦ weaken¹ t ⟧ (v₁ • ρ)
  ≡⟨ weaken-sound t (v₁ • ρ) ⟩
    ⟦ t ⟧ (⟦ ≼-refl ⟧ ρ)
  ≡⟨ cong ⟦ t ⟧ (⟦⟧-≼-refl ρ) ⟩
    ⟦ t ⟧ ρ
  ∎ where open ≡-Reasoning

≡-weaken² : ∀ {Γ τ} {τ₁ τ₂ : Type} (t : Term Γ τ) →
  ∀ (v₁ : ⟦ τ₁ ⟧) (v₂ : ⟦ τ₂ ⟧) (ρ : ⟦ Γ ⟧) → ⟦ weaken² t ⟧ (v₁ • v₂ • ρ) ≡ ⟦ t ⟧ ρ
≡-weaken² t v₁ v₂ ρ =
  begin
    ⟦ weaken² t ⟧ (v₁ • v₂ • ρ)
  ≡⟨ weaken-sound t (v₁ • v₂ • ρ) ⟩
    ⟦ t ⟧ (⟦ ≼-refl ⟧ ρ)
  ≡⟨ cong ⟦ t ⟧ (⟦⟧-≼-refl ρ) ⟩
    ⟦ t ⟧ ρ
  ∎ where open ≡-Reasoning

-- CORRECTNESS of NAMED TERMS

xor-term-correct : ∀ {Γ} (t₁ t₂ : Term Γ bool) →
  ∀ (ρ : ⟦ Γ ⟧) → ⟦ t₁ xor-term t₂ ⟧ ρ ≡ ⟦ t₁ ⟧ ρ xor ⟦ t₂ ⟧ ρ
xor-term-correct t₁ t₂ ρ
  with ⟦ t₁ ⟧ ρ | ⟦ t₂ ⟧ ρ
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

diff-term-correct : ∀ {τ Γ} {t₁ t₂ : Term Γ τ} →
  ∀ (ρ : ⟦ Γ ⟧) → ⟦ diff-term t₁ t₂ ⟧ ρ ≡ diff (⟦ t₁ ⟧ ρ) (⟦ t₂ ⟧ ρ)

apply-term-correct : ∀ {τ Γ} {t₁ : Term Γ (Δ-Type τ)} {t₂ : Term Γ τ} →
  ∀ (ρ : ⟦ Γ ⟧) → ⟦ apply-term t₁ t₂ ⟧ ρ ≡ apply (⟦ t₁ ⟧ ρ) (⟦ t₂ ⟧ ρ)

diff-term-correct {τ₁ ⇒ τ₂} {Γ} {f₁} {f₂} ρ = ext (λ dv → ext (λ v →
  begin
    (⟦ diff-term f₁ f₂ ⟧ ρ) dv v
  ≡⟨⟩
    ⟦ diff-term
       (app (weaken² f₁) (apply-term (var this) (var (that this))))
       (app (weaken² f₂) (var (that this))) ⟧ (v • dv • ρ)
  ≡⟨ diff-term-correct (v • dv • ρ) ⟩
    diff
      (⟦ app (weaken² f₁) (apply-term (var this) (var (that this))) ⟧ (v • dv • ρ))
      (⟦ app (weaken² f₂) (var (that this)) ⟧ (v • dv • ρ))
  ≡⟨⟩
    diff
      (⟦ weaken² f₁ ⟧ (v • dv • ρ) (⟦ apply-term (var this) (var (that this)) ⟧ (v • dv • ρ)))
      (⟦ weaken² f₂ ⟧ (v • dv • ρ) dv)
  ≡⟨ ≡-diff
       (≡-app (≡-weaken² f₁ v dv ρ) (apply-term-correct (v • dv • ρ)))
       (≡-app (≡-weaken² f₂ v dv ρ) ≡-refl) ⟩
    diff
      (⟦ f₁ ⟧ ρ (apply (⟦ var {_ • _ • _} this ⟧ (v • dv • ρ)) (⟦ var (that this) ⟧ (v • dv • ρ))))
      (⟦ f₂ ⟧ ρ dv)
  ≡⟨⟩
    diff (⟦ f₁ ⟧ ρ (apply v dv)) (⟦ f₂ ⟧Term ρ dv)
  ≡⟨⟩
    diff (⟦ f₁ ⟧ ρ) (⟦ f₂ ⟧ ρ) dv v
  ∎)) where open ≡-Reasoning

diff-term-correct {bool} {Γ} {b₁} {b₂} ρ =
  begin
    ⟦ diff-term b₁ b₂ ⟧ ρ
  ≡⟨⟩
    ⟦ b₁ xor-term b₂ ⟧ ρ
  ≡⟨ xor-term-correct b₁ b₂ ρ ⟩
    ⟦ b₁ ⟧ ρ xor ⟦ b₂ ⟧ ρ
  ≡⟨⟩
    diff (⟦ b₁ ⟧ ρ) (⟦ b₂ ⟧ ρ)
  ∎ where open ≡-Reasoning

apply-term-correct {τ₁ ⇒ τ₂} {Γ} {df} {f} ρ = ext (λ v →
  begin
    ⟦ apply-term df f ⟧ ρ v
  ≡⟨⟩
    ⟦ abs (apply-term
            (app (app (weaken¹ df) (var this))
                 (diff-term (var this) (var this)))
            (app (weaken¹ f) (var this))) ⟧ ρ v
  ≡⟨⟩
    ⟦ apply-term
        (app (app (weaken¹ df) (var this))
             (diff-term (var this) (var this)))
        (app (weaken¹ f) (var this)) ⟧ (v • ρ)
  ≡⟨ apply-term-correct (v • ρ) ⟩
    apply
      (⟦ app (app (weaken¹ df) (var this))
             (diff-term (var this) (var this)) ⟧ (v • ρ))
      (⟦ app (weaken¹ f) (var this) ⟧ (v • ρ))
  ≡⟨⟩
    apply
      (⟦ weaken¹ df ⟧ (v • ρ) v
        (⟦ diff-term (var this) (var this) ⟧ (v • ρ)))
      (⟦ weaken¹ f ⟧ (v • ρ) v)
  ≡⟨ ≡-apply
       (≡-app (≡-app (≡-weaken¹ df v ρ) ≡-refl)
              (diff-term-correct (v • ρ)))
       (≡-app (≡-weaken¹ f v ρ) ≡-refl) ⟩
    apply
      (⟦ df ⟧ ρ v
        (diff (⟦ var this ⟧ (v • ρ)) (⟦ var this ⟧ (v • ρ))))
      (⟦ f ⟧ ρ v)
  ≡⟨⟩
    apply (⟦ df ⟧ ρ v (diff v v)) (⟦ f ⟧ ρ v)
  ≡⟨ cong (λ X → apply (⟦ df ⟧ ρ v X) (⟦ f ⟧ ρ v)) (diff-derive v) ⟩
    apply (⟦ df ⟧ ρ v (derive v)) (⟦ f ⟧ ρ v)
  ≡⟨⟩
    apply (⟦ df ⟧ ρ) (⟦ f ⟧ ρ) v
  ∎) where open ≡-Reasoning

apply-term-correct {bool} {Γ} {db} {b} ρ =
  begin
    ⟦ apply-term db b ⟧ ρ
  ≡⟨⟩
    ⟦ db xor-term b ⟧ ρ
  ≡⟨ xor-term-correct db b ρ ⟩
    ⟦ db ⟧ ρ xor ⟦ b ⟧ ρ
  ≡⟨⟩
    apply (⟦ db ⟧ ρ) (⟦ b ⟧ ρ)
  ∎ where open ≡-Reasoning
