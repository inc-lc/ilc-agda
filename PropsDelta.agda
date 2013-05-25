module PropsDelta where

open import Relation.Binary.PropositionalEquality

open import Syntactic.Types
open import Syntactic.Contexts Type
open import Syntactic.Terms.Total

open import Denotational.Notation
open import Denotational.Values
open import Denotational.Environments Type ⟦_⟧Type
open import Denotational.Evaluation.Total
open import Denotational.Equivalence

open import Changes
open import ChangeContexts
open import ChangeContextLifting
open import Syntactic.Changes

-- PROPERTIES of Δ

Δ-abs : ∀ {τ₁ τ₂ Γ₁ Γ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t : Term (τ₁ • Γ₁) τ₂) →
  let Γ″ = keep Δ-Type τ₁ • keep τ₁ • Γ′ in
  Δ {{Γ′}} (abs t) ≈ abs (abs (Δ {τ₁ • Γ₁} t))
Δ-abs t = ext-t (λ ρ → refl)

Δ-app : ∀ {Γ₁ Γ₂ τ₁ τ₂} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}} (t₁ : Term Γ₁ (τ₁ ⇒ τ₂)) (t₂ : Term Γ₁ τ₁) →
  Δ {{Γ′}} (app t₁ t₂) ≈ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂)
Δ-app {{Γ′}} t₁ t₂ = ≈-sym (ext-t (λ ρ′ → let ρ = ⟦ Γ′ ⟧ ρ′ in
  begin
    ⟦ app (app (Δ {{Γ′}} t₁) (lift-term {{Γ′}} t₂)) (Δ {{Γ′}} t₂) ⟧ ρ′
  ≡⟨⟩
    diff
      (⟦ t₁ ⟧ (update ρ)
       (apply
         (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ)))
         (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′)))
      (⟦ t₁ ⟧ (ignore ρ) (⟦ lift-term {{Γ′}} t₂ ⟧ ρ′))
  ≡⟨ ≡-cong
       (λ x →
          diff
          (⟦ t₁ ⟧ (update ρ)
           (apply (diff (⟦ t₂ ⟧ (update ρ)) (⟦ t₂ ⟧ (ignore ρ))) x))
          (⟦ t₁ ⟧ (ignore ρ) x))
       (lift-term-ignore {{Γ′}} t₂) ⟩
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
  ≡⟨⟩
     ⟦ Δ {{Γ′}} (app t₁ t₂) ⟧ ρ′
  ∎)) where open ≡-Reasoning

private
  -- pulling out conditionals
  lemma₁ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    (f : A → B → C) (c₁ c₂ : Bool) {t₁ e₁ : A} {t₂ e₂ : B} →
    f (if c₁ then t₁ else e₁) (if c₂ then t₂ else e₂) ≡
    (if c₁ then (if c₂ then f t₁ t₂ else f t₁ e₂) else (if c₂ then f e₁ t₂ else f e₁ e₂))
  lemma₁ f true true = refl
  lemma₁ f true false = refl
  lemma₁ f false true = refl
  lemma₁ f false false = refl

  -- playing tricks with xor
  lemma₂ : ∀ {a b} {A : Set a} (B : Set b)
    (c₁ c₂ : Bool) {t₁ t₂ e₁ e₂ : A} →
    (if c₁ then (if c₂ then t₁ else e₁) else (if c₂ then t₂ else e₂)) ≡
    (if c₁ xor c₂ then (if c₂ then t₂ else e₁) else (if c₂ then t₁ else e₂))
  lemma₂ _ true true = refl
  lemma₂ _ true false = refl
  lemma₂ _ false true = refl
  lemma₂ _ false false = refl

  -- correctness of fake replacement changes
  lemma₃ : ∀ {Γ₁ Γ₂ τ} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}}
    (t₁ t₂ : Term Γ₁ τ) (ρ : ⟦ Γ₂ ⟧) →
    ⟦ diff-term (apply-term (Δ {{Γ′}} t₂)
                            (lift-term {{Γ′}} t₂))
                (lift-term {{Γ′}} t₁) ⟧ ρ
    ≡ diff (⟦ t₂ ⟧ (update (⟦ Γ′ ⟧ ρ)))
           (⟦ t₁ ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
  lemma₃ {Γ₁} {Γ₂} {{Γ′}} t₁ t₂ ρ =
    begin
      ⟦ diff-term (apply-term (Δ {{Γ′}} t₂) (lift-term {{Γ′}} t₂))
                  (lift-term {{Γ′}} t₁) ⟧ ρ
    ≡⟨ diff-term-correct ρ ⟩
      diff (⟦ apply-term (Δ {{Γ′}} t₂) (lift-term {{Γ′}} t₂) ⟧ ρ)
           (⟦ lift-term {{Γ′}} t₁ ⟧ ρ)
    ≡⟨ ≡-diff (apply-term-correct ρ) ≡-refl ⟩
      diff (apply (⟦ Δ {{Γ′}} t₂ ⟧ ρ)
                  (⟦ lift-term {{Γ′}} t₂ ⟧ ρ))
           (⟦ lift-term {{Γ′}} t₁ ⟧ ρ)
    ≡⟨ ≡-diff (≡-apply ≡-refl (lift-term-ignore {{Γ′}} t₂))
              (lift-term-ignore {{Γ′}} t₁) ⟩
      diff (apply (⟦ Δ {{Γ′}} t₂ ⟧ ρ)
                  (⟦ t₂ ⟧ (ignore (⟦ Γ′ ⟧ ρ))))
           (⟦ t₁ ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
    ≡⟨⟩
      diff (apply (diff (⟦ t₂ ⟧ (update (⟦ Γ′ ⟧ ρ)))
                        (⟦ t₂ ⟧ (ignore (⟦ Γ′ ⟧ ρ))))
                  (⟦ t₂ ⟧ (ignore (⟦ Γ′ ⟧ ρ))))
           (⟦ t₁ ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
    ≡⟨ ≡-diff (apply-diff (⟦ t₂ ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
                          (⟦ t₂ ⟧ (update (⟦ Γ′ ⟧ ρ))))
               ≡-refl ⟩
      diff (⟦ t₂ ⟧ (update (⟦ Γ′ ⟧ ρ)))
           (⟦ t₁ ⟧ (ignore (⟦ Γ′ ⟧ ρ)))
    ∎ where open ≡-Reasoning

Δ-if : ∀ {Γ₂ Γ₁ τ} {{Γ′ : Δ-Context Γ₁ ≼ Γ₂}}
  (t₁ : Term Γ₁ bool) (t₂ t₃ : Term Γ₁ τ) →
  Δ {{Γ′}} (if t₁ t₂ t₃) ≈
    if (Δ {{Γ′}} t₁)
       (if (lift-term {{Γ′}} t₁)
           (diff-term (apply-term (Δ {{Γ′}} t₃) (lift-term {{Γ′}} t₃))
                      (lift-term {{Γ′}} t₂))
           (diff-term (apply-term (Δ {{Γ′}} t₂) (lift-term {{Γ′}} t₂))
                      (lift-term {{Γ′}} t₃)))
       (if (lift-term {{Γ′}} t₁)
           (Δ {{Γ′}} t₂)
           (Δ {{Γ′}} t₃))
Δ-if {Γ₂} {Γ₁} {τ} {{Γ′}} t₁ t₂ t₃ = ext-t (λ ρ′ →
  let ρ = ⟦ Γ′ ⟧ ρ′
      ρ₁ = ignore ρ
      ρ₂ = update ρ
  in begin
      ⟦ Δ {{Γ′}} (if t₁ t₂ t₃) ⟧ ρ′
  ≡⟨⟩
    diff (if ⟦ t₁ ⟧ ρ₂ then ⟦ t₂ ⟧ ρ₂ else ⟦ t₃ ⟧ ρ₂)
         (if ⟦ t₁ ⟧ ρ₁ then ⟦ t₂ ⟧ ρ₁ else ⟦ t₃ ⟧ ρ₁)
  ≡⟨ lemma₁ diff (⟦ t₁ ⟧ ρ₂) (⟦ t₁ ⟧ ρ₁) ⟩
    (if ⟦ t₁ ⟧ ρ₂
     then (if ⟦ t₁ ⟧ ρ₁
           then diff (⟦ t₂ ⟧ ρ₂) (⟦ t₂ ⟧ ρ₁)
           else diff (⟦ t₂ ⟧ ρ₂) (⟦ t₃ ⟧ ρ₁))
     else (if ⟦ t₁ ⟧ ρ₁
           then diff (⟦ t₃ ⟧ ρ₂) (⟦ t₂ ⟧ ρ₁)
           else diff (⟦ t₃ ⟧ ρ₂) (⟦ t₃ ⟧ ρ₁)))
  ≡⟨ lemma₂ ⟦ Δ-Type τ ⟧ (⟦ t₁ ⟧ ρ₂) (⟦ t₁ ⟧ ρ₁) ⟩
    (if ⟦ t₁ ⟧ ρ₂ xor ⟦ t₁ ⟧ ρ₁
     then (if ⟦ t₁ ⟧ ρ₁
           then diff (⟦ t₃ ⟧ ρ₂) (⟦ t₂ ⟧ ρ₁)
           else diff (⟦ t₂ ⟧ ρ₂) (⟦ t₃ ⟧ ρ₁))
     else (if ⟦ t₁ ⟧ ρ₁
           then diff (⟦ t₂ ⟧ ρ₂) (⟦ t₂ ⟧ ρ₁)
           else diff (⟦ t₃ ⟧ ρ₂) (⟦ t₃ ⟧ ρ₁)))
  ≡⟨  ≡-if ≡-refl {v = ⟦ t₁ ⟧ ρ₂ xor ⟦ t₁ ⟧ ρ₁}
       then (≡-if ≡-sym (lift-term-ignore {{Γ′}} {ρ′} t₁)
             then ≡-sym (lemma₃ {{Γ′}} t₂ t₃ ρ′)
             else ≡-sym (lemma₃ {{Γ′}} t₃ t₂ ρ′) )
       else (≡-if ≡-sym (lift-term-ignore {{Γ′}} {ρ′} t₁)
             then ≡-refl
             else ≡-refl) ⟩
    ( if ⟦ t₁ ⟧ ρ₂ xor ⟦ t₁ ⟧ ρ₁
      then (if ⟦ lift-term {{Γ′}} t₁ ⟧ ρ′
            then ⟦ diff-term (apply-term (Δ {{Γ′}} t₃) (lift-term {{Γ′}} t₃))
                             (lift-term {{Γ′}} t₂) ⟧ ρ′
            else ⟦ diff-term (apply-term (Δ {{Γ′}} t₂) (lift-term {{Γ′}} t₂))
                             (lift-term {{Γ′}} t₃) ⟧ ρ′)
      else (if ⟦ lift-term {{Γ′}} t₁ ⟧ ρ′
            then ⟦ Δ {{Γ′}} t₂ ⟧ ρ′
            else ⟦ Δ {{Γ′}} t₃ ⟧ ρ′) )
  ≡⟨⟩
    ⟦ if (Δ {{Γ′}} t₁)
        (if (lift-term {{Γ′}} t₁)
            (diff-term (apply-term (Δ {{Γ′}} t₃) (lift-term {{Γ′}} t₃))
                       (lift-term {{Γ′}} t₂))
            (diff-term (apply-term (Δ {{Γ′}} t₂) (lift-term {{Γ′}} t₂))
                       (lift-term {{Γ′}} t₃)))
        (if (lift-term {{Γ′}} t₁)
            (Δ {{Γ′}} t₂)
            (Δ {{Γ′}} t₃)) ⟧ ρ′
  ∎) where open ≡-Reasoning
