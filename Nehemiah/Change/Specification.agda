------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Change evaluation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Specification where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Denotation.Value
open import Nehemiah.Denotation.Evaluation
open import Nehemiah.Change.Validity

import Base.Change.Algebra
open Base.Change.Algebra.FunctionChanges

open import Relation.Binary.PropositionalEquality
open import Data.Integer
open import Theorem.Groups-Nehemiah

import Parametric.Change.Specification
  Const ⟦_⟧Base ⟦_⟧Const as Specification

open import Algebra.Structures

private
  negate-correct-change : ∀ b db → negateBag (b ++ db) ++ negateBag emptyBag ≡
      negateBag b ++ negateBag db
  negate-correct-change b db = trans (a++negateBagEmptyBag≡a (negateBag (b ++ db))) (sym -a·-b=-ab)

-- add-correct-change-1 : ∀ a b c d →
--   a + (b + c) + (d + (+ 0)) ≡
--   a + b + (d + c)
-- add-correct-change-1 a b c d =
--   begin
--     a + (b + c) + (d + (+ 0))
--   ≡⟨ cong (λ □ → a + (b + c) + □) (right-id-int d) ⟩
--     (a + (b + c)) + d
--   ≡⟨ associative-int a (b + c) d ⟩
--     a + ((b + c) + d)
--   ≡⟨ cong (λ □ → a + □) (associative-int b c d) ⟩
--     a + (b + (c + d))
--   ≡⟨ sym (associative-int a b (c + d)) ⟩
--     (a + b) + (c + d)
--   ≡⟨ cong (λ □ → a + b + □) (commutative-int c d) ⟩
--     (a + b) + (d + c)
--   ∎
--   where
--     open ≡-Reasoning

  add-correct-change-1 : ∀ a b c d →
    a + (b + c) + (d + (+ 0)) ≡
    a + b + (d + c)
  add-correct-change-1 a b c d rewrite right-id-int d | associative-int a (b + c) d | associative-int b c d | sym (associative-int a b (c + d)) | commutative-int c d = refl

  add-correct-change-2 : ∀
    m n p q → m + n + p + q ≡ m + p + (n + q)
  add-correct-change-2 m n p q rewrite associative-int (m + n) p q = mn·pq=mp·nq {m}
  -- add-correct-change-2 m n p q =
  --   begin
  --     ((m + n) + p) + q
  --   ≡⟨ associative-int (m + n) p q ⟩
  --     (m + n) + (p + q)
  --   ≡⟨ mn·pq=mp·nq {m}⟩
  --     (m + p) + (n + q)
  --   ∎
  --   where
  --     open ≡-Reasoning

  sum-correct-change : ∀ b db → sumBag (b ++ db) + sumBag emptyBag ≡ sumBag b + sumBag db
  sum-correct-change b db rewrite sym (homo-sum {b ++ db} {emptyBag}) | right-id-bag (b ++ db) = homo-sum {b} {db}

  union-correct-change-1 : ∀ a da b db → (a ++ b ++ db) ++ (da ++ emptyBag) ≡ (a ++ b) ++ da ++ db
  union-correct-change-1 a da b db rewrite right-id-bag da | commutative-bag da db | sym (associative-bag (a ++ b) db da) | associative-bag a b db = refl

  union-correct-change-2 : ∀ a da b →
    ((a ++ da) ++ b) ++ emptyBag ++ emptyBag ≡ (a ++ b) ++ da ++ emptyBag
  union-correct-change-2 a da b rewrite right-id-bag emptyBag | right-id-bag da | right-id-bag ((a ++ da) ++ b) | associative-bag a da b | associative-bag a b da | commutative-bag da b = refl

  insert-correct-change-1 : ∀ n dn b db → (singletonBag n ++ b ++ db) ++
      (singletonBag (n + dn) ++ (b ++ db) ++ emptyBag) ++
      negateBag (singletonBag n ++ b ++ db)
      ≡
      (singletonBag n ++ b) ++
      (singletonBag (n + dn) ++ b ++ db) ++
      negateBag (singletonBag n ++ b)
  insert-correct-change-1 n dn b db rewrite right-id-bag (b ++ db) | a++[b\\a]=b {singletonBag n ++ b ++ db} {singletonBag (n + dn) ++ b ++ db} | a++[b\\a]=b {singletonBag n ++ b} {singletonBag (n + dn) ++ b ++ db} = refl
  insert-correct-change-2 : ∀ n dn b → (singletonBag (n + dn) ++ b) ++
      (singletonBag (n + dn + + 0) ++ b ++ emptyBag) ++
      negateBag (singletonBag (n + dn) ++ b)
      ≡
      (singletonBag n ++ b) ++
      (singletonBag (n + dn) ++ b ++ emptyBag) ++
      negateBag (singletonBag n ++ b)
  insert-correct-change-2 n dn b rewrite right-id-int (n + dn) | right-id-bag b | a++[b\\a]=b {singletonBag (n + dn) ++ b} {singletonBag (n + dn) ++ b} | a++[b\\a]=b {singletonBag n ++ b} {singletonBag (n + dn) ++ b} = refl

  open import Level using () renaming (zero to lzero)
  module caℤBag = FunctionChanges {c = lzero} {d = lzero} ℤ Bag

  flatmap-correct-change-1 :
    ∀ f (df : Δ f) b db →
         flatmapBag f (b ++ db)
      ++ flatmapBag (f ⊞ df) ((b ++ db) ++ emptyBag)
      ++ negateBag (flatmapBag f (b ++ db))
    ≡
        flatmapBag f b
      ++ flatmapBag (f ⊞ df) (b ++ db)
      ++ negateBag (flatmapBag f b)
  flatmap-correct-change-1 f df b db
   rewrite right-id-bag (b ++ db)
   | a++[b\\a]=b {flatmapBag f b} {flatmapBag (f ⊞ df) (b ++ db)}
   | a++[b\\a]=b {flatmapBag f (b ++ db)} {flatmapBag (f ⊞ df) (b ++ db)}
    = refl
  bar :
    ∀ (f : ℤ → Bag) (df : Δ f) a →
         (f a ++ apply df a (+ 0)) ++
         (f (a + + 0) ++ apply df (a + + 0) (+ 0)) ++
         negateBag (f a ++ apply df a (+ 0))
        ≡
         (f ⊞ df) a
  bar f df a
    rewrite right-id-int a
    | a++[b\\a]=b {f a ++ apply df a (+ 0)} {f a ++ apply df a (+ 0)}
    = refl

  open import Postulate.Extensionality
  flatmap-correct-change-2 :
    ∀ f (df : Δ {{caℤBag.changeAlgebra}} f) b →
      flatmapBag (λ a → f a ++ apply df a (+ 0)) b ++
      flatmapBag
      (λ a →
         (f a ++ apply df a (+ 0)) ++
         (f (a + + 0) ++ apply df (a + + 0) (+ 0)) ++
         negateBag (f a ++ apply df a (+ 0)))
      (b ++ emptyBag)
      ++ negateBag (flatmapBag (λ a → f a ++ apply df a (+ 0)) b)
    ≡
      flatmapBag f b ++
      flatmapBag (f ⊞ df) (b ++ emptyBag) ++
      negateBag (flatmapBag f b)
  flatmap-correct-change-2 f df b
    rewrite right-id-bag b | ext (bar f df)
    | a++[b\\a]=b {flatmapBag (f ⊞ df) b} {flatmapBag (f ⊞ df) b}
    | a++[b\\a]=b {flatmapBag f b} {flatmapBag (f ⊞ df) b}
    = refl
  ⟦_⟧ΔConst : ∀ {τ} → (c  : Const τ) → Δ₍ τ ₎ (⟦ c ⟧Const)
  ⟦ intlit-const n ⟧ΔConst = + 0
  ⟦ add-const ⟧ΔConst = record { apply = λ m dm → record { apply = λ n dn → dm + dn ; correct = λ n dn → add-correct-change-1 m n dn dm } ; correct = λ m dm → ext (λ n → add-correct-change-2 m dm n (+ 0)) }
  ⟦ minus-const ⟧ΔConst = record { apply = λ n dn → - dn ; correct = λ n dn → trans (right-id-int (- (n + dn))) (sym (-m·-n=-mn {n})) }
  ⟦ empty-const ⟧ΔConst = emptyBag
  ⟦ insert-const ⟧ΔConst = record { apply = λ n dn → record { apply = λ b db → (singletonBag (n + dn) ++ (b ++ db)) \\ (singletonBag n ++ b) ; correct = λ b db → insert-correct-change-1 n dn b db } ; correct = λ n dn → ext (λ b → insert-correct-change-2 n dn b) }
  ⟦ union-const ⟧ΔConst = record { apply = λ a da → record { apply = λ b db → da ++ db ; correct = λ b db → union-correct-change-1 a da b db } ; correct = λ a da → ext (λ b → union-correct-change-2 a da b) }
  ⟦ negate-const ⟧ΔConst = record { apply = λ b db → negateBag db ; correct = negate-correct-change }
  ⟦ flatmap-const ⟧ΔConst = record { apply = λ f df → record { apply = λ b db → flatmapBag (f ⊞₍ int ⇒ bag ₎ df) (b ++ db) \\ flatmapBag f b ; correct = λ b db → flatmap-correct-change-1 f df b db } ; correct = λ f df → ext (λ b → flatmap-correct-change-2 f df b) }
  ⟦ sum-const ⟧ΔConst = record { apply = λ b db → sumBag db ; correct = sum-correct-change }
--   correctness-const : ∀ {Σ τ} (c : Const τ) →
--     IsDerivative₍ Σ , τ ₎ ⟦ c ⟧Const ⟦ c ⟧ΔConst
--   correctness-const (intlit-const n) ∅ ∅ = right-id-int n
--   correctness-const add-const (n₁ • n₂ • ∅) (dn₁ • dn₂ • ∅) =
--     mn·pq=mp·nq {n₁} {n₂} {dn₁} {dn₂}
--   correctness-const minus-const (n • ∅) (dn • ∅) = -m·-n=-mn {n} {dn}
--   correctness-const empty-const ∅ ∅ = right-id-bag emptyBag
--   correctness-const insert-const (n • b • ∅) (dn • db • ∅) = a++[b\\a]=b
--   correctness-const union-const (b₁ • b₂ • ∅) (db₁ • db₂ • ∅) = ab·cd=ac·bd
--   correctness-const negate-const (b • ∅) (db • ∅) = -a·-b=-ab
--   correctness-const flatmap-const (f • b • ∅) (df • db • ∅) = a++[b\\a]=b
--   correctness-const sum-const (b • ∅) (db • ∅) = sym homo-sum
  union-correct : ∀ a b → (a ++ b) ++ (emptyBag ++ emptyBag) ≡ (a ++ b)
  union-correct a b = trans (cong (λ □ → (a ++ b) ++ □) (right-id-bag emptyBag)) (right-id-bag (a ++ b))
  negate-correct : ∀ b → negateBag b ++ negateBag emptyBag ≡ negateBag b
  --negate-correct b = trans (cong (λ □ → negateBag b ++ □) negateEmptyBag-emptyBag) (right-id-bag (negateBag b))
  negate-correct b rewrite negateEmptyBag-emptyBag | right-id-bag (negateBag b) = refl
  insert-correct : ∀ n b →
    (singletonBag n ++ b) ++
      (singletonBag (n + + 0) ++ b ++ emptyBag) ++
      negateBag (singletonBag n ++ b)
      ≡ singletonBag n ++ b
  -- insert-correct n b =
  --   begin
  --     (singletonBag n ++ b) ++
  --     (singletonBag (n + + 0) ++ b ++ emptyBag) ++
  --     negateBag (singletonBag n ++ b)
  --   ≡⟨ cong
  --        (λ □ →
  --           (singletonBag n ++ b) ++
  --           (singletonBag □ ++ b ++ emptyBag) ++
  --           negateBag (singletonBag n ++ b))
  --        (right-id-int n)
  --   ⟩
  --     (singletonBag n ++ b) ++
  --     (singletonBag n ++ b ++ emptyBag) ++
  --     negateBag (singletonBag n ++ b)
  --   ≡⟨ cong
  --        (λ □ →
  --          (singletonBag n ++ b) ++
  --          (singletonBag n ++ □) ++
  --          negateBag (singletonBag n ++ b)
  --        )
  --      (right-id-bag b)
  --   ⟩
  --     (singletonBag n ++ b) ++
  --     (singletonBag n ++ b) ++
  --     negateBag (singletonBag n ++ b)
  --   ≡⟨ cong (λ □ → (singletonBag n ++ b) ++ □) (right-inv-bag (singletonBag n ++ b)) ⟩
  --     (singletonBag n ++ b) ++
  --     emptyBag
  --   ≡⟨ right-id-bag (singletonBag n ++ b) ⟩
  --     singletonBag n ++ b
  --   ∎
  --   where open ≡-Reasoning
  insert-correct n b rewrite right-id-int n | right-id-bag b | right-inv-bag (singletonBag n ++ b) | right-id-bag (singletonBag n ++ b) = refl

  sum-correct : ∀ b → sumBag b + sumBag emptyBag ≡ sumBag b
  sum-correct b = trans (sym (homo-sum {b} {emptyBag})) (cong sumBag (right-id-bag b))

  foo : ∀ (f : ℤ → Bag) a → f a ++ (f (a + + 0) ++ negateBag (f a)) ≡ f a
  foo f a rewrite right-id-int a | right-inv-bag (f a) = right-id-bag (f a)

  flatmap-correct : ∀ f b →
    flatmapBag f b ++
      flatmapBag (λ a → f a ++ f (a + + 0) ++ negateBag (f a))
      (b ++ emptyBag)
      ++ negateBag (flatmapBag f b)
    ≡ flatmapBag f b
  flatmap-correct f b rewrite right-id-bag b | ext (foo f) | right-inv-bag (flatmapBag f b) = right-id-bag (flatmapBag f b)

  correctness-const : ∀ {τ} (c : Const τ) →
    ⟦ c ⟧Const ⊞₍ τ ₎ ⟦ c ⟧ΔConst ≡ ⟦ c ⟧Const
  correctness-const (intlit-const n) = right-id-int n
  correctness-const add-const = ext (λ m → ext (λ n → right-id-int (m + n)))
  correctness-const minus-const = ext (λ n → right-id-int (- n))
  correctness-const empty-const = right-id-bag emptyBag
  correctness-const insert-const = ext (λ n → ext (λ b → insert-correct n b))
  correctness-const union-const = ext (λ a → ext (λ b → union-correct a b))
  correctness-const negate-const = ext negate-correct
  correctness-const flatmap-const = ext (λ f → ext (λ b → flatmap-correct f b))
  correctness-const sum-const = ext (λ b → sum-correct b)


specification-structure : Specification.Structure
specification-structure = record
    { ⟦_⟧ΔConst = ⟦_⟧ΔConst
    ; correctness-const = correctness-const
    }

open Specification.Structure specification-structure public
