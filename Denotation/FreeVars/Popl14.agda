module Denotation.FreeVars.Popl14 where

-- Semantic significance of free variables in Calculus Popl14:
-- If all free variables of a term is irrelevant in a ΔEnv,
-- then the denotation of that term does not change.
-- In particular, closed terms cannot change.

open import Denotation.Specification.Canon-Popl14 public

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Integer
open import Syntax.FreeVars.Popl14 using (FV)
open import Theorem.Groups-Popl14
open import Theorem.CongApp
open import Postulate.Extensionality

-- Closed terms are unaffected by environments
unaffected : ∀ {τ Γ} {t : Term Γ τ} →
  FV t ≡ none → ∀ {ρ} → irrelevant (FV t) ρ
unaffected {t = t} eq {ρ} rewrite eq = irrelevance {ρ = ρ}

-- A variable's designated value does not change if it
-- is irrelevant in an environment.
stabilityVar : ∀ {τ Γ} {x : Var Γ τ} →
  ∀ {ρ : ΔEnv Γ} → irrelevant (singleton x) ρ →
  ⟦ x ⟧ (ignore ρ) ⊞ ⟦ x ⟧ΔVar ρ ≡ ⟦ x ⟧ (ignore ρ)

stabilityVar {x = this  } proof = proj₁ proof
stabilityVar {x = that y} proof = stabilityVar {x = y} proof

stability : ∀ {τ Γ} {t : Term Γ τ} {ρ : ΔEnv Γ} →
  irrelevant (FV t) ρ →
  ⟦ t ⟧ (ignore ρ) ⊞ ⟦ t ⟧Δ ρ ≡ ⟦ t ⟧ (ignore ρ)

-- Begin: Boilerplate for case t = abs s
stabilityAbs : ∀ {σ τ Γ} {t : Term (σ • Γ) τ} {ρ : ΔEnv Γ}
  (I : irrelevant (FV (abs t)) ρ) (v : ⟦ σ ⟧) →
    ⟦ t ⟧ (v • ignore ρ) ⊞
    ⟦ t ⟧Δ (cons v (v ⊟ v) (R[v,u-v] {u = v} {v}) ρ)
  ≡ ⟦ t ⟧ (v • ignore ρ)
stabilityAbs {t = t} {ρ} I v with FV t | inspect FV t
... | lack vars | [ case0 ] = stability {t = t} It where
  It : irrelevant (FV t) (cons v (v ⊟ v) (R[v,u-v] {u = v} {v}) ρ)
  It rewrite case0 = I
... | have vars | [ case1 ] = stability {t = t} It where
  It : irrelevant (FV t) (cons v (v ⊟ v) (R[v,u-v] {u = v} {v}) ρ)
  It rewrite case1 = v+[u-v]=u , I
-- End: Boilerplate

stability {t = intlit n} I = right-id-int n
stability {t = add s t} {ρ} I =
  let
    Is , It = project-irrelevance {ρ = ρ} I
  in
    trans (mn·pq=mp·nq
      {⟦ s ⟧ (ignore ρ)} {⟦ t ⟧ (ignore ρ)}
      {⟦ s ⟧Δ ρ} {⟦ t ⟧Δ ρ})
    (cong₂ _+_ (stability {t = s} Is) (stability {t = t} It))
stability {t = minus t} {ρ} I = trans
  (-m·-n=-mn {⟦ t ⟧ (ignore ρ)} {⟦ t ⟧Δ ρ})
  (cong -_ (stability {t = t} I))

stability {t = empty} I = right-id-bag emptyBag
stability {t = insert s t} {ρ} I =
  let
    n = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δn = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
    Is , It = project-irrelevance {ρ = ρ} I
  in
    begin
      (singletonBag n ++ b) ++
         (singletonBag (n ⊞ Δn) ++ (b ⊞ Δb)) \\ (singletonBag n ++ b)
    ≡⟨ a++[b\\a]=b ⟩
      singletonBag (n ⊞ Δn) ++ (b ⊞ Δb)
    ≡⟨ cong₂ _++_
         (cong singletonBag (stability {t = s} Is))
         (stability {t = t} It) ⟩
      singletonBag n ++ b
    ∎ where open ≡-Reasoning
stability {t = union s t} {ρ} I =
  let
    Is , It = project-irrelevance {ρ = ρ} I
  in
    trans (ab·cd=ac·bd
        {⟦ s ⟧ (ignore ρ)} {⟦ t ⟧ (ignore ρ)} {⟦ s ⟧Δ ρ} {⟦ t ⟧Δ ρ})
    (cong₂ _++_ (stability {t = s} Is) (stability {t = t} It))
stability {t = negate t} {ρ} I = trans
  (-a·-b=-ab {a = ⟦ t ⟧ (ignore ρ)} {⟦ t ⟧Δ ρ})
  (cong negateBag (stability {t = t} I))

stability {t = flatmap s t} {ρ} I =
  let
    f = ⟦ s ⟧ (ignore ρ)
    b = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δb = ⟦ t ⟧Δ ρ
    Is , It = project-irrelevance {ρ = ρ} I
    map = flatmapBag
  in
    begin
      map f b ⊞ (map (f ⊞ Δf) (b ⊞ Δb) ⊟ map f b)
    ≡⟨ a++[b\\a]=b ⟩
      map (f ⊞ Δf) (b ⊞ Δb)
    ≡⟨ cong₂ map (stability {t = s} Is) (stability {t = t} It) ⟩
      map f b
    ∎ where open ≡-Reasoning
stability {t = sum t} {ρ} I = trans (sym homo-sum)
  (cong sumBag (stability {t = t} I))

stability {t = var x} I = stabilityVar {x = x} I
stability {t = app s t} {ρ} I =
  let
    f = ⟦ s ⟧ (ignore ρ)
    v = ⟦ t ⟧ (ignore ρ)
    Δf = ⟦ s ⟧Δ ρ
    Δv = ⟦ t ⟧Δ ρ
    Is , It = project-irrelevance {ρ = ρ} I
  in
    begin
      f v ⊞ Δf v Δv (validity {t = t})
    ≡⟨ sym (corollary s t) ⟩
      (f ⊞ Δf) (v ⊞ Δv)
    ≡⟨ stability {t = s} Is ⟨$⟩ stability {t = t} It ⟩
      f v
    ∎ where open ≡-Reasoning
stability {t = abs t} I = ext (stabilityAbs {t = t} I)
