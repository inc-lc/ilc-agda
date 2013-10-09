module Popl14.Change.Specification where

-- Denotation-as-specification for Calculus Popl14
--
-- Contents
-- - ⟦_⟧Δ : binding-time-shifted derive
-- - Validity and correctness lemmas for ⟦_⟧Δ
-- - `corollary`: ⟦_⟧Δ reacts to both environment and arguments
-- - `corollary-closed`: binding-time-shifted main theorem

open import Popl14.Syntax.Term
open import Popl14.Denotation.Value
open import Popl14.Change.Validity
open import Popl14.Denotation.Evaluation public

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Integer
open import Structure.Bag.Popl14
open import Theorem.Groups-Popl14
open import Theorem.CongApp
open import Postulate.Extensionality

⟦_⟧Δ : ∀ {τ Γ} → (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) → Change τ (⟦ t ⟧ ρ)

correctness : ∀ {τ Γ} (t : Term Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ)
  → after {τ} (⟦ t ⟧Δ ρ dρ) ≡ ⟦ t ⟧ (update dρ)

⟦_⟧ΔVar : ∀ {τ Γ} → (x : Var Γ τ) → (ρ : ⟦ Γ ⟧) → ΔEnv Γ ρ → Change τ (⟦ x ⟧Var ρ)
⟦ this   ⟧ΔVar (v • ρ) (dv • dρ) = dv
⟦ that x ⟧ΔVar (v • ρ) (dv • dρ) = ⟦ x ⟧ΔVar ρ dρ

⟦_⟧Δ (intlit n) ρ dρ = + 0
⟦_⟧Δ (add s t) ρ dρ = ⟦ s ⟧Δ ρ dρ + ⟦ t ⟧Δ ρ dρ
⟦_⟧Δ (minus t) ρ dρ = - ⟦ t ⟧Δ ρ dρ
⟦_⟧Δ empty ρ dρ = emptyBag
⟦_⟧Δ (insert s t) ρ dρ =
  let
    n = ⟦ s ⟧ (ignore dρ)
    b = ⟦ t ⟧ (ignore dρ)
    Δn = ⟦ s ⟧Δ ρ dρ
    Δb = ⟦ t ⟧Δ ρ dρ
  in
    (singletonBag (n ⊞₍ int ₎ Δn) ++ (b ⊞₍ bag ₎ Δb)) ⊟₍ bag ₎ (singletonBag n ++ b)
⟦_⟧Δ (union s t) ρ dρ = ⟦ s ⟧Δ ρ dρ ++ ⟦ t ⟧Δ ρ dρ
⟦_⟧Δ (negate t) ρ dρ = negateBag (⟦ t ⟧Δ ρ dρ)
⟦_⟧Δ (flatmap s t) ρ dρ =
  let
    f = ⟦ s ⟧ ρ
    b = ⟦ t ⟧ ρ
    Δf : Change (int ⇒ bag) f
    Δf = ⟦ s ⟧Δ ρ dρ
    Δb = ⟦ t ⟧Δ ρ dρ
  in
    flatmapBag (f ⊞₍ int ⇒ bag ₎ Δf) (b ⊞₍ bag ₎ Δb) ⊟₍ bag ₎ flatmapBag f b
⟦_⟧Δ (sum t) ρ dρ = sumBag (⟦ t ⟧Δ ρ dρ)
⟦_⟧Δ (var x) ρ dρ = ⟦ x ⟧ΔVar ρ dρ
⟦_⟧Δ (app {σ} {τ} s t) ρ dρ =
     call-change (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)
⟦_⟧Δ (abs {σ} {τ} t) ρ dρ = cons
  (λ v dv → ⟦ t ⟧Δ (v • ρ) (dv • dρ))
  (λ v dv →
    begin
      ⟦ t ⟧ (v ⊞₍ σ ₎ dv • ρ)  ⊞₍ τ ₎
      ⟦ t ⟧Δ (v ⊞₍ σ ₎ dv • ρ) ((v ⊞₍ σ ₎ dv) ⊟₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ)
    ≡⟨  correctness t (v ⊞₍ σ ₎ dv • ρ) ((v ⊞₍ σ ₎ dv) ⊟₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ) ⟩
      ⟦ t ⟧ (update ((v ⊞₍ σ ₎ dv) ⊟₍ σ ₎ (v ⊞₍ σ ₎ dv) • dρ))
    ≡⟨⟩
      ⟦ t ⟧ (((v ⊞₍ σ ₎ dv) ⊞₍ σ ₎ ((v ⊞₍ σ ₎ dv) ⊟₍ σ ₎ (v ⊞₍ σ ₎ dv))) • update dρ)
    ≡⟨  cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ})  ⟩
      ⟦ t ⟧ (v ⊞₍ σ ₎ dv • update dρ)
    ≡⟨⟩
      ⟦ t ⟧ (update (dv • dρ))
    ≡⟨  sym (correctness t (v • ρ) (dv • dρ))  ⟩
      ⟦ t ⟧ (v • ρ)  ⊞₍ τ ₎  ⟦ t ⟧Δ (v • ρ) (dv • dρ)
    ∎) where open ≡-Reasoning

correctVar : ∀ {τ Γ} (x : Var Γ τ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) →
  ⟦ x ⟧ ρ ⊞₍ τ ₎ ⟦ x ⟧ΔVar ρ dρ ≡ ⟦ x ⟧ (update dρ)
correctVar (this) (v • ρ) (dv • dρ) = refl
correctVar (that y) (v • ρ) (dv • dρ) = correctVar y ρ dρ

correctness (intlit n) ρ dρ = right-id-int n
correctness (add s t) ρ dρ = trans
  (mn·pq=mp·nq
    {⟦ s ⟧ ρ} {⟦ t ⟧ ρ} {⟦ s ⟧Δ ρ dρ} {⟦ t ⟧Δ ρ dρ})
  (cong₂ _+_ (correctness s ρ dρ) (correctness t ρ dρ))
correctness (minus t) ρ dρ = trans
  (-m·-n=-mn {⟦ t ⟧ ρ} {⟦ t ⟧Δ ρ dρ})
  (cong -_ (correctness t ρ dρ))

correctness empty ρ dρ = right-id-bag emptyBag
correctness (insert s t) ρ dρ =
  let
    n = ⟦ s ⟧ ρ
    b = ⟦ t ⟧ ρ
    n′ = ⟦ s ⟧ (update dρ)
    b′ = ⟦ t ⟧ (update dρ)
    Δn = ⟦ s ⟧Δ ρ dρ
    Δb = ⟦ t ⟧Δ ρ dρ
  in
    begin
      (singletonBag n ++ b) ++
         (singletonBag (n ⊞₍ base base-int ₎ Δn) ++
           (b ⊞₍ base base-bag ₎ Δb)) \\ (singletonBag n ++ b)
    ≡⟨ a++[b\\a]=b ⟩
      singletonBag (n ⊞₍ base base-int ₎ Δn) ++
        (b ⊞₍ base base-bag ₎ Δb)
    ≡⟨ cong₂ _++_
         (cong singletonBag (correctness s ρ dρ))
         (correctness t ρ dρ) ⟩
      singletonBag n′ ++ b′
    ∎ where open ≡-Reasoning
correctness (union s t) ρ dρ = trans
  (ab·cd=ac·bd
    {⟦ s ⟧ ρ} {⟦ t ⟧ ρ} {⟦ s ⟧Δ ρ dρ} {⟦ t ⟧Δ ρ dρ})
  (cong₂ _++_ (correctness s ρ dρ) (correctness t ρ dρ))
correctness (negate t) ρ dρ = trans
  (-a·-b=-ab {⟦ t ⟧ ρ} {⟦ t ⟧Δ ρ dρ})
  (cong negateBag (correctness t ρ dρ))

correctness (flatmap s t) ρ dρ =
  let
    f = ⟦ s ⟧ ρ
    b = ⟦ t ⟧ ρ
    Δf = ⟦ s ⟧Δ ρ dρ
    Δb = ⟦ t ⟧Δ ρ dρ
  in trans
      (a++[b\\a]=b {flatmapBag f b}
        {flatmapBag (f ⊞₍ base base-int ⇒ base base-bag ₎ Δf)
                    (b ⊞₍ base base-bag ₎ Δb)})
      (cong₂ flatmapBag (correctness s ρ dρ) (correctness t ρ dρ))
correctness (sum t) ρ dρ =
  let
    b = ⟦ t ⟧ ρ
    Δb = ⟦ t ⟧Δ ρ dρ
  in
    trans (sym homo-sum) (cong sumBag (correctness t ρ dρ))

correctness {τ} (var x) ρ dρ = correctVar {τ} x ρ dρ
correctness (app {σ} {τ} s t) ρ dρ =
  let
    f = ⟦ s ⟧ ρ
    g = ⟦ s ⟧ (update dρ)
    u = ⟦ t ⟧ ρ
    v = ⟦ t ⟧ (update dρ)
    Δf = ⟦ s ⟧Δ ρ dρ
    Δu = ⟦ t ⟧Δ ρ dρ
  in
    begin
      f u ⊞₍ τ ₎ call-change Δf u Δu
    ≡⟨  sym (is-valid Δf u Δu) ⟩
       (f ⊞₍ σ ⇒ τ ₎ Δf) (u ⊞₍ σ ₎ Δu)
    ≡⟨ correctness {σ ⇒ τ} s ρ dρ ⟨$⟩ correctness {σ} t ρ dρ ⟩
      g v
    ∎ where open ≡-Reasoning
correctness {σ ⇒ τ} {Γ} (abs t) ρ dρ = ext (λ v →
  let
    -- dρ′ : ΔEnv (σ • Γ) (v • ρ)
    dρ′ = nil-change σ v • dρ
  in
    begin
      ⟦ t ⟧ (ignore dρ′) ⊞₍ τ ₎ ⟦ t ⟧Δ _ dρ′
    ≡⟨ correctness {τ} t _ dρ′ ⟩
      ⟦ t ⟧ (update dρ′)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ}) ⟩
      ⟦ t ⟧ (v • update dρ)
    ∎
  ) where open ≡-Reasoning

-- Corollary: (f ⊞ df) (v ⊞ dv) = f v ⊞ df v dv

corollary : ∀ {σ τ Γ}
  (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) (ρ : ⟦ Γ ⟧) (dρ : ΔEnv Γ ρ) →
    (⟦ s ⟧ ρ ⊞₍ σ ⇒ τ ₎ ⟦ s ⟧Δ ρ dρ)
      (⟦ t ⟧ ρ ⊞₍ σ ₎ ⟦ t ⟧Δ ρ dρ)
  ≡ (⟦ s ⟧ ρ) (⟦ t ⟧ ρ)
    ⊞₍ τ ₎
    (call-change (⟦ s ⟧Δ ρ dρ)) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

corollary {σ} {τ} s t ρ dρ =
  is-valid (⟦ s ⟧Δ ρ dρ) (⟦ t ⟧ ρ) (⟦ t ⟧Δ ρ dρ)

corollary-closed : ∀ {σ τ} (t : Term ∅ (σ ⇒ τ))
  (v : ⟦ σ ⟧) (dv : Change σ v)
  → ⟦ t ⟧ ∅ (after {σ} dv)
  ≡ ⟦ t ⟧ ∅ v ⊞₍ τ ₎ call-change (⟦ t ⟧Δ ∅ ∅) v dv

corollary-closed {σ} {τ} t v dv =
  let
    f  = ⟦ t ⟧ ∅
    Δf = ⟦ t ⟧Δ ∅ ∅
  in
    begin
      f (after {σ} dv)
    ≡⟨ cong (λ hole → hole (after {σ} dv))
            (sym (correctness {σ ⇒ τ} t ∅ ∅)) ⟩
      (f ⊞₍ σ ⇒ τ ₎ Δf) (after {σ} dv)
    ≡⟨ is-valid (⟦ t ⟧Δ ∅ ∅) v dv ⟩
      f (before {σ} dv) ⊞₍ τ ₎ call-change Δf v dv
    ∎ where open ≡-Reasoning
