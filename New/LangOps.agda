{-# OPTIONS --allow-unsolved-metas #-}
module New.LangOps where

open import Data.List.All
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Integer

open import New.Lang
open import New.Changes
open import New.LangChanges

oplusτo : ∀ {Γ} τ → Term Γ (τ ⇒ Δt τ ⇒ τ)
ominusτo : ∀ {Γ} τ → Term Γ (τ ⇒ τ ⇒ Δt τ)

onilτo : ∀ {Γ} τ → Term Γ (τ ⇒ Δt τ)
onilτo τ = abs (app₂ (ominusτo τ) (var this) (var this))

oplusτo (σ ⇒ τ) = abs (abs (abs
  (app₂ (oplusτo τ)
    (app (var (that (that this))) (var this))
    (app₂ (var (that this)) (var this) (app (onilτo σ) (var this))))))
oplusτo int = const plus
oplusτo (pair σ τ) = abs (abs (app₂ (const cons)
  (app₂ (oplusτo σ) (app (const fst) (var (that this))) (app (const fst) (var this)))
  (app₂ (oplusτo τ) (app (const snd) (var (that this))) (app (const snd) (var this)))))
oplusτo (sum σ τ) = {!!}

ominusτo (σ ⇒ τ) = abs (abs (abs (abs (app₂ (ominusτo τ)
  (app (var (that (that (that this)))) (app₂ (oplusτo σ) (var (that this)) (var this)))
  (app (var (that (that this))) (var (that this)))))))
ominusτo int = const minus
ominusτo (pair σ τ) = abs (abs (app₂ (const cons)
  (app₂ (ominusτo σ) (app (const fst) (var (that this))) (app (const fst) (var this)))
  (app₂ (ominusτo τ) (app (const snd) (var (that this))) (app (const snd) (var this)))))
ominusτo (sum σ τ) = {!!}

open import Postulate.Extensionality

syntax oplusτo t a da = a ⊞[ t ] da

oplusτ : ∀ τ → ⟦ τ ⟧Type → ⟦ Δt τ ⟧Type → ⟦ τ ⟧Type

oplusτ τ = ⟦ oplusτo τ ⟧Term ∅
ominusτ : ∀ τ → ⟦ τ ⟧Type → ⟦ τ ⟧Type → ⟦ Δt τ ⟧Type
ominusτ τ = ⟦ ominusτo τ ⟧Term ∅

⟦oplusτ⟧ : ∀ τ → ⟦ τ ⟧Type → ⟦ Δt τ ⟧Type → ⟦ τ ⟧Type
⟦ominusτ⟧ : ∀ τ → ⟦ τ ⟧Type → ⟦ τ ⟧Type → ⟦ Δt τ ⟧Type
⟦oplusτ⟧ τ = _⊕_
⟦ominusτ⟧ τ = _⊝_

oplusτ-equiv : ∀ Γ (ρ : ⟦ Γ ⟧Context) τ a da → ⟦ oplusτo τ ⟧Term ρ a da ≡ ⟦oplusτ⟧ τ a da
ominusτ-equiv : ∀ Γ (ρ : ⟦ Γ ⟧Context) τ a da → ⟦ ominusτo τ ⟧Term ρ a da ≡ ⟦ominusτ⟧ τ a da

oplusτ-equiv-ext : ∀ τ → oplusτ τ ≡ ⟦oplusτ⟧ τ
oplusτ-equiv-ext τ = ext (λ a → ext (oplusτ-equiv ∅ ∅ τ a))
ominusτ-equiv-ext : ∀ τ → ominusτ τ ≡ ⟦ominusτ⟧ τ
ominusτ-equiv-ext τ = ext (λ a → ext (ominusτ-equiv ∅ ∅ τ a))

oplusτ-equiv Γ ρ (σ ⇒ τ) f df = ext (λ a → lemma a)
  where
    module _ (a : ⟦ σ ⟧Type) where
      ρ′ : ⟦ σ • Δt (σ ⇒ τ) • (σ ⇒ τ) • Γ ⟧Context
      ρ′ = a ∷ df ∷ f ∷ ρ
      ρ′′ = a ∷ ρ′
      lemma : ⟦ oplusτo τ ⟧Term ρ′ (f a)
         (df a (⟦ ominusτo σ ⟧Term ρ′′ a a))
         ≡ ⟦oplusτ⟧ τ (f a) (df a (⟦ominusτ⟧ σ a a))
      lemma
        rewrite ominusτ-equiv _ ρ′′ σ a a
        | oplusτ-equiv _ ρ′ τ (f a) (df a (⟦ominusτ⟧ σ a a))
        = refl
oplusτ-equiv Γ ρ int a da = refl
oplusτ-equiv Γ ρ (pair σ τ) (a , b) (da , db)
  rewrite oplusτ-equiv _ ((da , db) ∷ (a , b) ∷ ρ) σ a da
  | oplusτ-equiv _ ((da , db) ∷ (a , b) ∷ ρ) τ b db
  = refl
oplusτ-equiv Γ ρ (sum σ τ) s ds = {!!}

ominusτ-equiv Γ ρ (σ ⇒ τ) g f = ext (λ a → ext (lemma a))
  where
    module _ (a : ⟦ σ ⟧Type) (da : Cht σ) where
      ρ′ = da ∷ a ∷ f ∷ g ∷ ρ
      lemma : ⟦ ominusτo τ ⟧Term (da ∷ a ∷ f ∷ g ∷ ρ)
        (g (⟦ oplusτo σ ⟧Term (da ∷ a ∷ f ∷ g ∷ ρ) a da)) (f a)
        ≡ ⟦ominusτ⟧ τ (g (⟦oplusτ⟧ σ a da)) (f a)
      lemma
        rewrite oplusτ-equiv _ ρ′ σ a da
        | ominusτ-equiv _ ρ′ τ (g (⟦oplusτ⟧ σ a da)) (f a) = refl
ominusτ-equiv Γ ρ int b a = refl
ominusτ-equiv Γ ρ (pair σ τ) (a2 , b2) (a1 , b1)
  rewrite ominusτ-equiv _ ((a1 , b1) ∷ (a2 , b2) ∷ ρ) σ a2 a1
  | ominusτ-equiv _ ((a1 , b1) ∷ (a2 , b2) ∷ ρ) τ b2 b1
  = refl
ominusτ-equiv Γ ρ (sum σ τ) s2 s1 = {!!}

-- synIsChAlgτ : (τ : Type) → IsChAlg ⟦ τ ⟧Type ⟦ Δt τ ⟧Type (oplusτ τ) (ominusτ τ)

-- synChAlgt : (τ : Type) → ChAlg ⟦ τ ⟧Type
-- synChAlgt τ = record { Ch = Cht τ ; _⊕_ = oplusτ τ ; _⊝_ = ominusτ τ ; isChAlg = isChAlgτ τ}
-- private
--   instance
--     synIchAlgt : ∀ {τ} → ChAlg ⟦ τ ⟧Type
-- synIchAlgt {τ} = chAlgt τ

-- synIsChAlgτ τ rewrite oplusτ-equiv-ext τ | ominusτ-equiv-ext τ = ⟦isChAlgτ⟧ τ

-- oplusτo-invariant : ∀ τ {Γ₁ Γ₂} (ρ₁ : ⟦ Γ₁ ⟧Context) (ρ₂ : ⟦ Γ₂ ⟧Context) →
--   ⟦ oplusτo τ ⟧Term ρ₁ ≡ ⟦ oplusτo τ ⟧Term ρ₂
-- ominusτo-invariant : ∀ τ {Γ₁ Γ₂} (ρ₁ : ⟦ Γ₁ ⟧Context) (ρ₂ : ⟦ Γ₂ ⟧Context) →
--   ⟦ ominusτo τ ⟧Term ρ₁ ≡ ⟦ ominusτo τ ⟧Term ρ₂
-- ominusτo-invariant (σ ⇒ τ) ρ₁ ρ₂ = {!!}
-- ominusτo-invariant int ρ₁ ρ₂ = refl
-- ominusτo-invariant (pair σ τ) ρ₁ ρ₂ = {!!}
-- ominusτo-invariant (sum σ τ) ρ₁ ρ₂ = {!!}
-- oplusτo-invariant (σ ⇒ τ) ρ₁ ρ₂ = ext³ lemma
--   where
--     module _ (f : ⟦ σ ⇒ τ ⟧Type) (df : Cht (σ ⇒ τ)) (a : ⟦ σ ⟧Type) where
--       ρ₁′ = a ∷ df ∷ f ∷ ρ₁
--       ρ₁′′ = a ∷ ρ₁′
--       ρ₂′ = a ∷ df ∷ f ∷ ρ₂
--       ρ₂′′ = a ∷ ρ₂′
--       lemma : ⟦ oplusτo τ ⟧Term (a ∷ df ∷ f ∷ ρ₁) (f a)
--         (df a (⟦ ominusτo σ ⟧Term (a ∷ a ∷ df ∷ f ∷ ρ₁) a a))
--         ≡
--         ⟦ oplusτo τ ⟧Term (a ∷ df ∷ f ∷ ρ₂) (f a)
--         (df a (⟦ ominusτo σ ⟧Term (a ∷ a ∷ df ∷ f ∷ ρ₂) a a))
--       lemma  rewrite oplusτo-invariant τ ρ₁′ ρ₂′ | ominusτo-invariant σ ρ₁′′ ρ₂′′ = refl
-- oplusτo-invariant int ρ₁ ρ₂ = refl
-- oplusτo-invariant (pair σ τ) ρ₁ ρ₂ = ext (λ p → ext (lemma p))
--   where
--     module _ (p : ⟦ pair σ τ ⟧Type) (dp : Cht (pair σ τ)) where
--       ρ₁′ = dp ∷ p ∷ ρ₁
--       ρ₂′ = dp ∷ p ∷ ρ₂
--       lemma :
--         (⟦ oplusτo σ ⟧Term (dp ∷ p ∷ ρ₁) (proj₁ p) (proj₁ dp) ,
--          ⟦ oplusτo τ ⟧Term (dp ∷ p ∷ ρ₁) (proj₂ p) (proj₂ dp))
--         ≡
--         (⟦ oplusτo σ ⟧Term (dp ∷ p ∷ ρ₂) (proj₁ p) (proj₁ dp) ,
--          ⟦ oplusτo τ ⟧Term (dp ∷ p ∷ ρ₂) (proj₂ p) (proj₂ dp))
--       lemma rewrite oplusτo-invariant σ ρ₁′ ρ₂′ | oplusτo-invariant τ ρ₁′ ρ₂′ = refl
-- oplusτo-invariant (sum σ τ) ρ₁ ρ₂ = {!!}
