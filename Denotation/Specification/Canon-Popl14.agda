module Denotation.Specification.Canon-Popl14 where

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
⟦_⟧Δ : ∀ {τ Γ} → (t : Term Γ τ) (dρ : ΔEnv Γ) → Change τ

-- better name is: ⟦_⟧Δ reacts to future arguments
validity : ∀ {τ Γ} (t : Term Γ τ) (dρ : ΔEnv Γ) →
  valid {τ} (⟦ t ⟧ (ignore dρ)) (⟦ t ⟧Δ dρ)

-- better name is: ⟦_⟧Δ reacts to free variables
correctness : ∀ {τ Γ} (t : Term Γ τ) (dρ : ΔEnv Γ)
  → ⟦ t ⟧ (ignore dρ) ⊞₍ τ ₎ ⟦ t ⟧Δ dρ ≡ ⟦ t ⟧ (update dρ)

⟦_⟧ΔVar : ∀ {τ Γ} → Var Γ τ → ΔEnv Γ → Change τ
⟦ this   ⟧ΔVar (cons v dv R[v,dv] • dρ) = dv
⟦ that x ⟧ΔVar (cons v dv R[v,dv] • dρ) = ⟦ x ⟧ΔVar dρ

⟦_⟧Δ (intlit n) dρ = + 0
⟦_⟧Δ (add s t) dρ = ⟦ s ⟧Δ dρ + ⟦ t ⟧Δ dρ
⟦_⟧Δ (minus t) dρ = - ⟦ t ⟧Δ dρ
⟦_⟧Δ empty dρ = emptyBag
⟦_⟧Δ (insert s t) dρ =
  let
    n = ⟦ s ⟧ (ignore dρ)
    b = ⟦ t ⟧ (ignore dρ)
    Δn = ⟦ s ⟧Δ dρ
    Δb = ⟦ t ⟧Δ dρ
  in
    (singletonBag (n ⊞₍ int ₎ Δn) ++ (b ⊞₍ bag ₎ Δb)) ⊟₍ bag ₎ (singletonBag n ++ b)
⟦_⟧Δ (union s t) dρ = ⟦ s ⟧Δ dρ ++ ⟦ t ⟧Δ dρ
⟦_⟧Δ (negate t) dρ = negateBag (⟦ t ⟧Δ dρ)
⟦_⟧Δ (flatmap s t) dρ =
  let
    f = ⟦ s ⟧ (ignore dρ)
    b = ⟦ t ⟧ (ignore dρ)
    Δf = ⟦ s ⟧Δ dρ
    Δb = ⟦ t ⟧Δ dρ
  in
    flatmapBag (f ⊞₍ int ⇒ bag ₎ Δf) (b ⊞₍ bag ₎ Δb) ⊟₍ bag ₎ flatmapBag f b
⟦_⟧Δ (sum t) dρ = sumBag (⟦ t ⟧Δ dρ)
⟦_⟧Δ (var x) dρ = ⟦ x ⟧ΔVar dρ
⟦_⟧Δ (app {σ} {τ} s t) dρ =
     (⟦ s ⟧Δ dρ) (cons (⟦ t ⟧ (ignore dρ)) (⟦ t ⟧Δ dρ)
  (validity {σ} t dρ))
⟦_⟧Δ (abs t) dρ = λ v →
  ⟦ t ⟧Δ (v • dρ)

validVar : ∀ {τ Γ} (x : Var Γ τ) →
  (dρ : ΔEnv Γ) → valid {τ} (⟦ x ⟧ (ignore dρ)) (⟦ x ⟧ΔVar dρ)
validVar this (cons v Δv R[v,Δv] • _) = R[v,Δv]
validVar {τ} (that x) (cons _ _ _ • dρ) = validVar {τ} x dρ

validity (intlit n)    dρ = tt
validity (add s t)     dρ = tt
validity (minus t)     dρ = tt
validity (empty)       dρ = tt
validity (insert s t)  dρ = tt
validity (union s t)   dρ = tt
validity (negate t)    dρ = tt
validity (flatmap s t) dρ = tt
validity (sum t)       dρ = tt

validity {τ} (var x) dρ = validVar {τ} x dρ

validity (app s t) dρ =
  let
    v = ⟦ t ⟧ (ignore dρ)
    Δv = ⟦ t ⟧Δ dρ
  in
    proj₁ (validity s dρ (cons v Δv (validity t dρ)))

validity {σ ⇒ τ} (abs t) dρ = λ v →
  let
    v′ = after {σ} v
    Δv′ = v′ ⊟₍ σ ₎ v′
    dρ₁ = v • dρ
    dρ₂ = nil-valid-change σ v′ • dρ
  in
    validity t dρ₁
    ,
    (begin
      ⟦ t ⟧ (ignore dρ₂) ⊞₍ τ ₎ ⟦ t ⟧Δ dρ₂
    ≡⟨ correctness t dρ₂ ⟩
      ⟦ t ⟧ (update dρ₂)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ}) ⟩
      ⟦ t ⟧ (update dρ₁)
    ≡⟨ sym (correctness t dρ₁) ⟩
      ⟦ t ⟧ (ignore dρ₁) ⊞₍ τ ₎ ⟦ t ⟧Δ dρ₁
    ∎) where open ≡-Reasoning

correctVar : ∀ {τ Γ} {x : Var Γ τ} {dρ : ΔEnv Γ} →
  ⟦ x ⟧ (ignore dρ) ⊞₍ τ ₎ ⟦ x ⟧ΔVar dρ ≡ ⟦ x ⟧ (update dρ)
correctVar {x = this  } {cons v dv R[v,dv] • dρ} = refl
correctVar {x = that y} {cons v dv R[v,dv] • dρ} = correctVar {x = y} {dρ}

correctness (intlit n) dρ = right-id-int n
correctness (add s t) dρ = trans
  (mn·pq=mp·nq
    {⟦ s ⟧ (ignore dρ)} {⟦ t ⟧ (ignore dρ)} {⟦ s ⟧Δ dρ} {⟦ t ⟧Δ dρ})
  (cong₂ _+_ (correctness s dρ) (correctness t dρ))
correctness (minus t) dρ = trans
  (-m·-n=-mn {⟦ t ⟧ (ignore dρ)} {⟦ t ⟧Δ dρ})
  (cong -_ (correctness t dρ))

correctness empty dρ = right-id-bag emptyBag
correctness (insert s t) dρ =
  let
    n = ⟦ s ⟧ (ignore dρ)
    b = ⟦ t ⟧ (ignore dρ)
    n′ = ⟦ s ⟧ (update dρ)
    b′ = ⟦ t ⟧ (update dρ)
    Δn = ⟦ s ⟧Δ dρ
    Δb = ⟦ t ⟧Δ dρ
  in
    begin
      (singletonBag n ++ b) ++
         (singletonBag (n ⊞₍ base base-int ₎ Δn) ++
           (b ⊞₍ base base-bag ₎ Δb)) \\ (singletonBag n ++ b)
    ≡⟨ a++[b\\a]=b ⟩
      singletonBag (n ⊞₍ base base-int ₎ Δn) ++
        (b ⊞₍ base base-bag ₎ Δb)
    ≡⟨ cong₂ _++_
         (cong singletonBag (correctness s dρ))
         (correctness t dρ) ⟩
      singletonBag n′ ++ b′
    ∎ where open ≡-Reasoning
correctness (union s t) dρ = trans
  (ab·cd=ac·bd
    {⟦ s ⟧ (ignore dρ)} {⟦ t ⟧ (ignore dρ)} {⟦ s ⟧Δ dρ} {⟦ t ⟧Δ dρ})
  (cong₂ _++_ (correctness s dρ) (correctness t dρ))
correctness (negate t) dρ = trans
  (-a·-b=-ab {⟦ t ⟧ (ignore dρ)} {⟦ t ⟧Δ dρ})
  (cong negateBag (correctness t dρ))

correctness (flatmap s t) dρ =
  let
    f = ⟦ s ⟧ (ignore dρ)
    b = ⟦ t ⟧ (ignore dρ)
    Δf = ⟦ s ⟧Δ dρ
    Δb = ⟦ t ⟧Δ dρ
  in trans
      (a++[b\\a]=b {flatmapBag f b}
        {flatmapBag (f ⊞₍ base base-int ⇒ base base-bag ₎ Δf)
                    (b ⊞₍ base base-bag ₎ Δb)})
      (cong₂ flatmapBag (correctness s dρ) (correctness t dρ))
correctness (sum t) dρ =
  let
    b = ⟦ t ⟧ (ignore dρ)
    Δb = ⟦ t ⟧Δ dρ
  in
    trans (sym homo-sum) (cong sumBag (correctness t dρ))

correctness {τ} (var x) dρ = correctVar {τ} {x = x}
correctness (app {σ} {τ} s t) dρ =
  let
    f = ⟦ s ⟧ (ignore dρ)
    g = ⟦ s ⟧ (update dρ)
    u = ⟦ t ⟧ (ignore dρ)
    v = ⟦ t ⟧ (update dρ)
    Δf = ⟦ s ⟧Δ dρ
    Δu = ⟦ t ⟧Δ dρ
  in
    begin
      f u ⊞₍ τ ₎ Δf (cons u Δu (validity {σ} t dρ))
    ≡⟨ sym (proj₂ (validity {σ ⇒ τ} s dρ (cons u Δu (validity {σ} t dρ)))) ⟩
      (f ⊞₍ σ ⇒ τ ₎ Δf) (u ⊞₍ σ ₎ Δu)
    ≡⟨ correctness {σ ⇒ τ} s dρ ⟨$⟩ correctness {σ} t dρ ⟩
      g v
    ∎ where open ≡-Reasoning
correctness {σ ⇒ τ} {Γ} (abs t) dρ = ext (λ v →
  let
    dρ′ : ΔEnv (σ • Γ)
    dρ′ = nil-valid-change σ v • dρ
  in
    begin
      ⟦ t ⟧ (ignore dρ′) ⊞₍ τ ₎ ⟦ t ⟧Δ dρ′
    ≡⟨ correctness {τ} t dρ′ ⟩
      ⟦ t ⟧ (update dρ′)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update dρ)) (v+[u-v]=u {σ}) ⟩
      ⟦ t ⟧ (v • update dρ)
    ∎
  ) where open ≡-Reasoning

-- Corollary: (f ⊞ df) (v ⊞ dv) = f v ⊞ df v dv
corollary : ∀ {σ τ Γ}
  (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) {dρ : ΔEnv Γ} →
    (⟦ s ⟧ (ignore dρ) ⊞₍ σ ⇒ τ ₎ ⟦ s ⟧Δ dρ)
      (⟦ t ⟧ (ignore dρ) ⊞₍ σ ₎ ⟦ t ⟧Δ dρ)
  ≡ (⟦ s ⟧ (ignore dρ)) (⟦ t ⟧ (ignore dρ))
    ⊞₍ τ ₎
    (⟦ s ⟧Δ dρ) (cons (⟦ t ⟧ (ignore dρ)) (⟦ t ⟧Δ dρ) (validity {σ} t dρ))

corollary {σ} {τ} s t {dρ} = proj₂
  (validity {σ ⇒ τ} s dρ (cons (⟦ t ⟧ (ignore dρ))
     (⟦ t ⟧Δ dρ) (validity {σ} t dρ)))

corollary-closed : ∀ {σ τ} {t : Term ∅ (σ ⇒ τ)}
  (v : ValidChange σ)
  → ⟦ t ⟧ ∅ (after {σ} v)
  ≡ ⟦ t ⟧ ∅ (before {σ} v) ⊞₍ τ ₎ ⟦ t ⟧Δ ∅ v

corollary-closed {σ} {τ} {t = t} v =
  let
    f  = ⟦ t ⟧ ∅
    Δf = ⟦ t ⟧Δ ∅
  in
    begin
      f (after {σ} v)
    ≡⟨ cong (λ hole → hole (after {σ} v))
            (sym (correctness {σ ⇒ τ} t ∅)) ⟩
      (f ⊞₍ σ ⇒ τ ₎ Δf) (after {σ} v)
    ≡⟨ proj₂ (validity {σ ⇒ τ} t ∅ v) ⟩
      f (before {σ} v) ⊞₍ τ ₎ Δf v
    ∎ where open ≡-Reasoning
