module Base.Change.Equivalence.Realizers where

open import Relation.Binary.PropositionalEquality
open import Base.Change.Algebra
open import Level
open import Data.Unit
open import Data.Product
open import Function
open import Postulate.Extensionality

open import Base.Change.Equivalence

-- Here we give lemmas about realizers for function changes. Using these lemmas,
-- you can simply write a "realizer" for a derivative for f (that is, the
-- computational part of the derivative, without any embedded proof), show
-- separately that it's change-equivalent to the nil change for f and get a
-- proper function change; this code proves the needed validity lemmas.
--
-- Given a type of codes for types, such lemmas should be provable by induction
-- on those types; something similar is done in the proof of erasure, though
-- details are quite different.
--
-- For now, we do something close to unrolling the induction manually for
-- functions of arity 1, 2 and 3 since those are actually used in the codebase.
-- I didn't actually write the induction though, and I'm not sure how to do it.
--
-- So there are two attempts which might give ideas; one is
-- equiv-raw-change-to-change-binary and equiv-raw-change-to-change-ternary, the
-- other is equiv-raw-change-to-change-binary′ and
-- equiv-raw-change-to-change-ternary′.
module _
  {a} {A : Set a} {{CA : ChangeAlgebra A}}
  {b} {B : Set b} {{CB : ChangeAlgebra B}}
  (f : A → B)
  where
  private
    Set′ = Set (a ⊔ b)

  equiv₁ : ∀ (df′ : Δ f) (df-realizer : RawChange f) → Set′
  equiv₁ df′ df-realizer = apply df′ ≡ df-realizer

  equiv-raw-change-to-change-ResType :
    ∀ (df-realizer : RawChange f) → Set′
  equiv-raw-change-to-change-ResType df-realizer =
    Σ[ df′ ∈ Δ f ] equiv₁ df′ df-realizer

  equiv-hp :
      ∀ (df : Δ f) (df-realizer : RawChange f) → Set′
  equiv-hp df df-realizer = (∀ a da → apply df a da ≙₍ f a ₎ df-realizer a da)

  -- This is sort of the "base case" of the proof mentioned above.
  equiv-raw-change-to-change :
    ∀ (df : Δ f) (df-realizer : RawChange f) →
      equiv-hp df df-realizer →
      equiv-raw-change-to-change-ResType df-realizer
  equiv-raw-change-to-change df df-realizer ≙df = record { apply = df-realizer ; correct = df-realizer-correct} , refl
    where
      df-realizer-correct : ∀ a da → f (a ⊞ da) ⊞ df-realizer (a ⊞ da) (nil (a ⊞ da)) ≡ f a ⊞ df-realizer a da
      df-realizer-correct a da
        rewrite sym (proof (≙df a da))
        | sym (proof (≙df (a ⊞ da) (nil (a ⊞ da))))
        = correct df a da

  equiv-raw-deriv-to-deriv :
    ∀ (df-realizer : RawChange f) →
      equiv-hp (nil f) df-realizer →
      IsDerivative f df-realizer
  equiv-raw-deriv-to-deriv df-realizer ≙df with equiv-raw-change-to-change (nil f) df-realizer ≙df
  equiv-raw-deriv-to-deriv .(FunctionChanges.apply nil-f) ≙df | nil-f , refl =
    equiv-nil-is-derivative nil-f (delta-ext ≙df)

module _
  {a} {A : Set a} {{CA : ChangeAlgebra A}}
  {b} {B : Set b} {{CB : ChangeAlgebra B}}
  {c} {C : Set c} {{CC : ChangeAlgebra C}}
  (f : A → B → C) where
  private
    Set′ = Set (a ⊔ b ⊔ c)

  -- This is, sort of, an instance of the inductive step in the proof mentioned above.
  RawChangeBinary :
    Set′
  RawChangeBinary = ∀ a (da : Δ a) → RawChange (f a)

  equiv-hp-binary : ∀ (df : Δ f) (df-realizer : RawChangeBinary) → Set′
  equiv-hp-binary df df-realizer =
    ∀ a da → equiv-hp (f a) (apply df a da) (df-realizer a da)

  equiv₂ : ∀ (df′ : Δ f) (df-realizer : RawChangeBinary) → Set′
  equiv₂ df′ df-realizer = ∀ a da → equiv₁ (f a) (apply df′ a da) (df-realizer a da)

  equiv-raw-change-to-change-binary-ResType :
    ∀ (df-realizer : RawChangeBinary) → Set′
  equiv-raw-change-to-change-binary-ResType df-realizer =
    Σ[ df′ ∈ Δ f ] equiv₂ df′ df-realizer

  equiv-raw-change-to-change-binary equiv-raw-change-to-change-binary′ :
    ∀ (df : Δ f) (df-realizer : RawChangeBinary) →
      equiv-hp-binary df df-realizer →
      equiv-raw-change-to-change-binary-ResType df-realizer
  equiv-raw-change-to-change-binary df df-realizer ≙df = proj₁ (equiv-raw-change-to-change f df df₁′ ≙df₁′) , λ a da → refl
    where
      module _ (a : A) (da : Δ a) where
        f₁ = f a
        df₁ : Δ f₁
        df₁ = apply df a da
        df-realizer₁ = df-realizer a da
        ≙df₁ = ≙df a da
        df-realizer₁-correct : ∀ b db → f₁ (b ⊞ db) ⊞ df-realizer₁ (b ⊞ db) (nil (b ⊞ db)) ≡ f₁ b ⊞ df-realizer₁ b db
        df-realizer₁-correct b db
          rewrite sym (proof (≙df₁ b db))
          | sym (proof (≙df₁ (b ⊞ db) (nil (b ⊞ db))))
          = correct df₁ b db
        df₁′ : Δ f₁
        df₁′ = record { apply = df-realizer₁ ; correct = df-realizer₁-correct }
        ≙df₁′ : df₁ ≙₍ f₁ ₎ df₁′
        ≙df₁′ = delta-ext ≙df₁

  equiv-raw-change-to-change-binary′ df df-realizer ≙df = record { apply = df₁′ ; correct = λ a da → ext (df-realizer-correct a da) } , λ a da → refl
    where
      module _ (a : A) (da : Δ a) where
        f₁ = f a
        df₁ : Δ f₁
        df₁ = apply df a da
        df-realizer₁ = df-realizer a da
        ≙df₁ = ≙df a da
        df₁′ = proj₁ (equiv-raw-change-to-change f₁ df₁ df-realizer₁ ≙df₁)
        df-realizer-correct : ∀ b → f (a ⊞ da) b ⊞ df-realizer (a ⊞ da) (nil (a ⊞ da)) b (nil b) ≡ f a b ⊞ df-realizer a da b (nil b)
        df-realizer-correct b
          rewrite sym (proof (≙df a da b (nil b)))
          | sym (proof (≙df (a ⊞ da) (nil (a ⊞ da)) b (nil b)))
          = cong (λ □ → □ b) (correct df a da)

  equiv-raw-deriv-to-deriv-binary :
    ∀ (df-realizer : RawChangeBinary) →
      (≙df : equiv-hp-binary (nil f) df-realizer) →
      IsDerivative f (apply (proj₁ (equiv-raw-change-to-change-binary (nil f) df-realizer ≙df)))
  equiv-raw-deriv-to-deriv-binary df-realizer ≙df a da with equiv-raw-change-to-change-binary (nil f) df-realizer ≙df
  ... | nil-f , nil-f≡df with sym (nil-f≡df a da)
  ... | df-a-da≡nil-f-a-da rewrite df-a-da≡nil-f-a-da = equiv-nil-is-derivative nil-f (delta-ext {df = nil f} {dg = nil-f} (λ a da → doe (ext (lemma a da)))) a da
    where
      lemma : ∀ a da b → (f a ⊞ apply (nil f) a da) b ≡ (f a ⊞ apply nil-f a da) b
      lemma a da b rewrite nil-f≡df a da = proof (≙df a da b (nil b))

module _
  {a} {A : Set a} {{CA : ChangeAlgebra A}}
  {b} {B : Set b} {{CB : ChangeAlgebra B}}
  {c} {C : Set c} {{CC : ChangeAlgebra C}}
  {d} {D : Set d} {{CD : ChangeAlgebra D}}
  (f : A → B → C → D)
  where
  private
    Set′ = Set (a ⊔ b ⊔ c ⊔ d)

  -- This is an adapted copy of the above "inductive step".
  RawChangeTernary : Set′
  RawChangeTernary = ∀ a (da : Δ a) → RawChangeBinary (f a)

  equiv-hp-ternary : ∀ (df : Δ f) (df-realizer : RawChangeTernary) → Set′
  equiv-hp-ternary df df-realizer =
    ∀ a da → equiv-hp-binary (f a) (apply df a da) (df-realizer a da)

  equiv₃ : ∀ (df′ : Δ f) (df-realizer : RawChangeTernary) → Set′
  equiv₃ df′ df-realizer = ∀ a da → equiv₂ (f a) (apply df′ a da) (df-realizer a da)

  equiv-raw-change-to-change-ternary-ResType :
    ∀ (df-realizer : RawChangeTernary) → Set′
  equiv-raw-change-to-change-ternary-ResType df-realizer =
    Σ[ df′ ∈ Δ f ] equiv₃ df′ df-realizer

  equiv-raw-change-to-change-ternary equiv-raw-change-to-change-ternary′ :
    ∀ (df : Δ f) (df-realizer : RawChangeTernary) →
      equiv-hp-ternary df df-realizer →
      equiv-raw-change-to-change-ternary-ResType df-realizer

  equiv-raw-change-to-change-ternary df df-realizer ≙df =
    proj₁ (equiv-raw-change-to-change-binary f df df₁′ ≙df₁′) , λ a da b db → refl
    where
      module _ (a : A) (da : Δ a) (b : B) (db : Δ b) where
        f₁ = f a b
        df₁ : Δ f₁
        df₁ = apply (apply df a da) b db
        df-realizer₁ = df-realizer a da b db
        ≙df₁ = ≙df a da b db

        df-realizer₁-correct : ∀ c dc → f₁ (c ⊞ dc) ⊞ df-realizer₁ (c ⊞ dc) (nil (c ⊞ dc)) ≡ f₁ c ⊞ df-realizer₁ c dc
        df-realizer₁-correct c dc
          rewrite sym (proof (≙df₁ c dc))
          | sym (proof (≙df₁ (c ⊞ dc) (nil (c ⊞ dc))))
          = correct df₁ c dc
        df₁′ : Δ f₁
        df₁′ = record { apply = df-realizer₁ ; correct = df-realizer₁-correct }
        ≙df₁′ : df₁ ≙₍ f₁ ₎ df₁′
        ≙df₁′ = delta-ext ≙df₁

  equiv-raw-change-to-change-ternary′ df df-realizer ≙df = record { apply = df₁′ ; correct = λ a da → ext (λ b → ext (df-realizer-correct a da b)) } , λ a da b db → refl
    where
      module _ (a : A) (da : Δ a) where
        f₁ = f a
        df₁ : Δ f₁
        df₁ = apply df a da
        df-realizer₁ = df-realizer a da
        ≙df₁ = ≙df a da
        df₁′ = proj₁ (equiv-raw-change-to-change-binary f₁ df₁ df-realizer₁ ≙df₁)
        df-realizer-correct : ∀ b c → f (a ⊞ da) b c ⊞ df-realizer (a ⊞ da) (nil (a ⊞ da)) b (nil b) c (nil c) ≡ f a b c ⊞ df-realizer a da b (nil b) c (nil c)
        df-realizer-correct b c
          rewrite sym (proof (≙df a da b (nil b) c (nil c)))
          | sym (proof (≙df (a ⊞ da) (nil (a ⊞ da)) b (nil b) c (nil c)))
          = cong (λ □ → □ b c) (correct df a da)
