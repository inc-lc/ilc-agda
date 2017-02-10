module New.LangOps where

open import Data.List.All
open import Data.Sum
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

-- Do NOT try to read this, such terms are write-only. But the behavior is
-- specified to be oplusτ-equiv and ominusτ-equiv.
oplusτo (σ ⇒ τ) = abs (abs (abs
  (app₂ (oplusτo τ)
    (app (var (that (that this))) (var this))
    (app₂ (var (that this)) (var this) (app (onilτo σ) (var this))))))
oplusτo int = const plus
oplusτo (pair σ τ) = abs (abs (app₂ (const cons)
  (app₂ (oplusτo σ) (app (const fst) (var (that this))) (app (const fst) (var this)))
  (app₂ (oplusτo τ) (app (const snd) (var (that this))) (app (const snd) (var this)))))
oplusτo (sum σ τ) = abs (abs (app₃ (const match) (var (that this))
  (abs (app₃ (const match) (var (that this))
    (abs (app₃ (const match) (var this)
      (abs (app (const linj) (app₂ (oplusτo σ) (var (that (that this))) (var this))))
      (abs (app (const linj) (var (that (that this)))))))
    (abs (var this))))
  (abs (app₃ (const match) (var (that this))
    (abs (app₃ (const match) (var this)
      (abs (app (const rinj) (var (that (that this)))))
      (abs (app (const rinj) (app₂ (oplusτo τ) (var (that (that this))) (var this))))))
    (abs (var this))))))

ominusτo (σ ⇒ τ) = abs (abs (abs (abs (app₂ (ominusτo τ)
  (app (var (that (that (that this)))) (app₂ (oplusτo σ) (var (that this)) (var this)))
  (app (var (that (that this))) (var (that this)))))))
ominusτo int = const minus
ominusτo (pair σ τ) = abs (abs (app₂ (const cons)
  (app₂ (ominusτo σ) (app (const fst) (var (that this))) (app (const fst) (var this)))
  (app₂ (ominusτo τ) (app (const snd) (var (that this))) (app (const snd) (var this)))))
ominusτo (sum σ τ) = abs (abs (app₃ (const match) (var (that this))
  (abs (app₃ (const match) (var (that this))
    (abs (app (const linj) (app (const linj) (app₂ (ominusτo σ) (var (that this)) (var this)))))
    (abs (app (const rinj) (var (that (that (that this))))))))
  -- (app (const {!!}) {!ominusτo σ!}) {!!}
  (abs (app₃ (const match) (var (that this))
    (abs (app (const rinj) (var (that (that (that this))))))
    (abs (app (const linj) (app (const rinj) (app₂ (ominusτo τ) (var (that this)) (var this)))))))))

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

oplusτ-equiv-ext : ∀ τ Γ → ⟦ oplusτo {Γ} τ ⟧Term ≡ λ ρ → ⟦oplusτ⟧ τ
oplusτ-equiv-ext τ _ = ext³ (λ ρ a da → oplusτ-equiv _ ρ τ a da)
ominusτ-equiv-ext : ∀ τ Γ → ⟦ ominusτo {Γ} τ ⟧Term ≡ λ ρ → ⟦ominusτ⟧ τ
ominusτ-equiv-ext τ _ = ext³ (λ ρ a da → ominusτ-equiv _ ρ τ a da)

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
oplusτ-equiv Γ ρ (sum σ τ) (inj₁ x) (inj₁ (inj₁ dx))
  rewrite oplusτ-equiv-ext σ (Δt σ • sum (Δt σ) (Δt τ) • σ • Δt (sum σ τ) • sum σ τ • Γ)
  = refl
oplusτ-equiv Γ ρ (sum σ τ) (inj₁ x) (inj₁ (inj₂ dy)) = refl
oplusτ-equiv Γ ρ (sum σ τ) (inj₁ x) (inj₂ y) = refl
oplusτ-equiv Γ ρ (sum σ τ) (inj₂ y) (inj₁ (inj₁ dx)) = refl
oplusτ-equiv Γ ρ (sum σ τ) (inj₂ y) (inj₁ (inj₂ dy))
  rewrite oplusτ-equiv-ext τ (Δt τ • sum (Δt σ) (Δt τ) • τ • Δt (sum σ τ) • sum σ τ • Γ)
  = refl
oplusτ-equiv Γ ρ (sum σ τ) (inj₂ y) (inj₂ y₁) = refl

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
ominusτ-equiv Γ ρ (sum σ τ) (inj₁ x) (inj₁ x₁)
  rewrite ominusτ-equiv-ext σ (σ • σ • sum σ τ • sum σ τ • Γ)
  = refl
ominusτ-equiv Γ ρ (sum σ τ) (inj₁ x) (inj₂ y) = refl
ominusτ-equiv Γ ρ (sum σ τ) (inj₂ y) (inj₁ x) = refl
ominusτ-equiv Γ ρ (sum σ τ) (inj₂ y) (inj₂ y₁)
  rewrite ominusτ-equiv-ext τ (τ • τ • sum σ τ • sum σ τ • Γ)
  = refl
