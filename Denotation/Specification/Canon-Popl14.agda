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
⟦_⟧Δ : ∀ {τ Γ} → (t : Term Γ τ) (ρ : ΔEnv Γ) → Change τ

-- better name is: ⟦_⟧Δ reacts to future arguments
validity : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  valid {τ} (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ ρ)

-- better name is: ⟦_⟧Δ reacts to free variables
correctness : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ}
  → ⟦ t ⟧ (ignore ρ) ⊞₍ τ ₎ ⟦ t ⟧Δ ρ ≡ ⟦ t ⟧ (update ρ)

⟦_⟧ΔVar : ∀ {τ Γ} → Var Γ τ → ΔEnv Γ → Change τ
⟦ this   ⟧ΔVar (cons v dv R[v,dv] • ρ) = dv
⟦ that x ⟧ΔVar (cons v dv R[v,dv] • ρ) = ⟦ x ⟧ΔVar ρ

⟦_⟧Δ (intlit n) ρ = + 0
⟦_⟧Δ (add s t) ρ = ⟦ s ⟧Δ ρ + ⟦ t ⟧Δ ρ
⟦_⟧Δ (minus t) ρ = - ⟦ t ⟧Δ ρ
⟦_⟧Δ empty ρ = emptyBag
⟦_⟧Δ (insert s t) ρ =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δn = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
  in
    (singletonBag (n ⊞₍ int ₎ Δn) ++ (b ⊞₍ bag ₎ Δb)) ⊟₍ bag ₎ (singletonBag n ++ b)
⟦_⟧Δ (union s t) ρ = ⟦ s ⟧Δ ρ ++ ⟦ t ⟧Δ ρ
⟦_⟧Δ (negate t) ρ = negateBag (⟦ t ⟧Δ ρ)
⟦_⟧Δ (flatmap s t) ρ =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
  in
    flatmapBag (f ⊞₍ int ⇒ bag ₎ Δf) (b ⊞₍ bag ₎ Δb) ⊟₍ bag ₎ flatmapBag f b
⟦_⟧Δ (sum t) ρ = sumBag (⟦ t ⟧Δ ρ)
⟦_⟧Δ (var x) ρ = ⟦ x ⟧ΔVar ρ
⟦_⟧Δ (app {σ} {τ} s t) ρ = 
     (⟦ s ⟧Δ ρ) (cons (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ ρ)
  (validity {σ} {t = t}))
⟦_⟧Δ (abs t) ρ = λ v →
  ⟦ t ⟧Δ (v • ρ)

validVar : ∀ {τ Γ} (x : Var Γ τ) →
  ∀ {ρ : ΔEnv Γ} → valid {τ} (⟦ x ⟧ (ignore ρ)) (⟦ x ⟧ΔVar ρ)
validVar this {cons v Δv R[v,Δv] • _} = R[v,Δv]
validVar {τ} (that x) {cons _ _ _ • ρ} = validVar {τ} x

validity {t = intlit n}    = tt
validity {t = add s t}     = tt
validity {t = minus t}     = tt
validity {t = empty}       = tt
validity {t = insert s t}  = tt
validity {t = union s t}   = tt
validity {t = negate t}    = tt
validity {t = flatmap s t} = tt
validity {t = sum t}       = tt

validity {τ} {t = var x} = validVar {τ} x

validity {t = app s t} {ρ} =
  let
    v = ⟦ t ⟧ (ignore ρ)
    Δv = ⟦ t ⟧Δ ρ
  in
    proj₁ (validity {t = s} {ρ} (cons v Δv (validity {t = t} {ρ})))

validity {σ ⇒ τ} {t = abs t} {ρ} = λ v →
  let
    v′ = after {σ} v
    Δv′ = v′ ⊟₍ σ ₎ v′
    ρ₁ = v • ρ
    ρ₂ = nil-valid-change σ v′ • ρ
  in
    validity {t = t} {ρ₁}
    ,
    (begin
      ⟦ t ⟧ (ignore ρ₂) ⊞₍ τ ₎ ⟦ t ⟧Δ ρ₂
    ≡⟨ correctness {t = t} {ρ₂} ⟩
      ⟦ t ⟧ (update ρ₂)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) (v+[u-v]=u {σ}) ⟩
      ⟦ t ⟧ (update ρ₁)
    ≡⟨ sym (correctness {t = t} {ρ₁}) ⟩
      ⟦ t ⟧ (ignore ρ₁) ⊞₍ τ ₎ ⟦ t ⟧Δ ρ₁
    ∎) where open ≡-Reasoning

correctVar : ∀ {τ Γ} {x : Var Γ τ} {ρ : ΔEnv Γ} →
  ⟦ x ⟧ (ignore ρ) ⊞₍ τ ₎ ⟦ x ⟧ΔVar ρ ≡ ⟦ x ⟧ (update ρ)
correctVar {x = this  } {cons v dv R[v,dv] • ρ} = refl
correctVar {x = that y} {cons v dv R[v,dv] • ρ} = correctVar {x = y} {ρ}

correctness {t = intlit n} = right-id-int n
correctness {t = add s t} {ρ} = trans
  (mn·pq=mp·nq
    {⟦ s ⟧ (ignore ρ)} {⟦ t ⟧ (ignore ρ)} {⟦ s ⟧Δ ρ} {⟦ t ⟧Δ ρ})
  (cong₂ _+_ (correctness {t = s}) (correctness {t = t}))
correctness {t = minus t} {ρ} = trans
  (-m·-n=-mn {⟦ t ⟧ (ignore ρ)} {⟦ t ⟧Δ ρ})
  (cong -_ (correctness {t = t}))

correctness {t = empty} = right-id-bag emptyBag
correctness {t = insert s t} {ρ} =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    n′ = ⟦ s ⟧ (update ρ)
    b′ = ⟦ t ⟧ (update ρ)
    Δn = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
  in
    begin
      (singletonBag n ++ b) ++
         (singletonBag (n ⊞₍ base base-int ₎ Δn) ++
           (b ⊞₍ base base-bag ₎ Δb)) \\ (singletonBag n ++ b)
    ≡⟨ a++[b\\a]=b ⟩
      singletonBag (n ⊞₍ base base-int ₎ Δn) ++
        (b ⊞₍ base base-bag ₎ Δb)
    ≡⟨ cong₂ _++_
         (cong singletonBag (correctness {t = s}))
         (correctness {t = t}) ⟩
      singletonBag n′ ++ b′
    ∎ where open ≡-Reasoning
correctness {t = union s t} {ρ} = trans
  (ab·cd=ac·bd
    {⟦ s ⟧ (ignore ρ)} {⟦ t ⟧ (ignore ρ)} {⟦ s ⟧Δ ρ} {⟦ t ⟧Δ ρ})
  (cong₂ _++_ (correctness {t = s}) (correctness {t = t}))
correctness {t = negate t} {ρ} = trans
  (-a·-b=-ab {⟦ t ⟧ (ignore ρ)} {⟦ t ⟧Δ ρ})
  (cong negateBag (correctness {t = t}))

correctness {t = flatmap s t} {ρ} =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
  in trans
      (a++[b\\a]=b {flatmapBag f b}
        {flatmapBag (f ⊞₍ base base-int ⇒ base base-bag ₎ Δf)
                    (b ⊞₍ base base-bag ₎ Δb)})
      (cong₂ flatmapBag (correctness {t = s}) (correctness {t = t}))
correctness {t = sum t} {ρ} =
  let
    b = ⟦ t ⟧ (ignore ρ)
    Δb = ⟦ t ⟧Δ ρ
  in
    trans (sym homo-sum) (cong sumBag (correctness {t = t}))

correctness {τ} {t = var x} = correctVar {τ} {x = x}
correctness {t = app {σ} {τ} s t} {ρ} =
  let
    f = ⟦ s ⟧ (ignore ρ)
    g = ⟦ s ⟧ (update ρ)
    u = ⟦ t ⟧ (ignore ρ)
    v = ⟦ t ⟧ (update ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δu = ⟦ t ⟧Δ ρ
  in
    begin
      f u ⊞₍ τ ₎ Δf (cons u Δu (validity {σ} {t = t}))
    ≡⟨ sym (proj₂ (validity {σ ⇒ τ} {t = s} (cons u Δu (validity {σ} {t = t})))) ⟩
      (f ⊞₍ σ ⇒ τ ₎ Δf) (u ⊞₍ σ ₎ Δu)
    ≡⟨ correctness {σ ⇒ τ} {t = s} ⟨$⟩ correctness {σ} {t = t} ⟩
      g v
    ∎ where open ≡-Reasoning
correctness {σ ⇒ τ} {Γ} {abs t} {ρ} = ext (λ v →
  let
    ρ′ : ΔEnv (σ • Γ)
    ρ′ = nil-valid-change σ v • ρ
  in
    begin
      ⟦ t ⟧ (ignore ρ′) ⊞₍ τ ₎ ⟦ t ⟧Δ ρ′
    ≡⟨ correctness {τ} {t = t} {ρ′} ⟩
      ⟦ t ⟧ (update ρ′)
    ≡⟨ cong (λ hole → ⟦ t ⟧ (hole • update ρ)) (v+[u-v]=u {σ}) ⟩
      ⟦ t ⟧ (v • update ρ)
    ∎
  ) where open ≡-Reasoning

-- Corollary: (f ⊞ df) (v ⊞ dv) = f v ⊞ df v dv
corollary : ∀ {σ τ Γ}
  (s : Term Γ (σ ⇒ τ)) (t : Term Γ σ) {ρ : ΔEnv Γ} →
    (⟦ s ⟧ (ignore ρ) ⊞₍ σ ⇒ τ ₎ ⟦ s ⟧Δ ρ)
      (⟦ t ⟧ (ignore ρ) ⊞₍ σ ₎ ⟦ t ⟧Δ ρ)
  ≡ (⟦ s ⟧ (ignore ρ)) (⟦ t ⟧ (ignore ρ))
    ⊞₍ τ ₎
    (⟦ s ⟧Δ ρ) (cons (⟦ t ⟧ (ignore ρ)) (⟦ t ⟧Δ ρ) (validity {σ} {t = t}))

corollary {σ} {τ} s t {ρ} = proj₂
  (validity {σ ⇒ τ} {t = s} (cons (⟦ t ⟧ (ignore ρ))
     (⟦ t ⟧Δ ρ) (validity {σ} {t = t})))

corollary-closed : ∀ {σ τ} {t : Term ∅ (σ ⇒ τ)}
  {v : ⟦ σ ⟧} {Δv : Change σ} {R[v,Δv] : valid {σ} v Δv}
  → ⟦ t ⟧ ∅ (v ⊞₍ σ ₎ Δv)
  ≡ ⟦ t ⟧ ∅ v ⊞₍ τ ₎ ⟦ t ⟧Δ ∅ (cons v Δv R[v,Δv])

corollary-closed {σ} {τ} {t = t} {v} {Δv} {R[v,Δv]} =
  let
    f  = ⟦ t ⟧ ∅
    Δf = ⟦ t ⟧Δ ∅
  in
    begin
      f (v ⊞₍ σ ₎ Δv)
    ≡⟨ cong (λ hole → hole (v ⊞₍ σ ₎ Δv))
            (sym (correctness {σ ⇒ τ} {t = t})) ⟩
      (f ⊞₍ σ ⇒ τ ₎ Δf) (v ⊞₍ σ ₎ Δv)
    ≡⟨ proj₂ (validity {σ ⇒ τ} {t = t} (cons v Δv R[v,Δv])) ⟩
      f v ⊞₍ τ ₎ Δf (cons v Δv R[v,Δv])
    ∎ where open ≡-Reasoning
