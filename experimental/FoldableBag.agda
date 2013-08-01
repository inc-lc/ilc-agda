module experimental.FoldableBag where

open import experimental.FoldableBagParametric
import Level as L

open import Algebra
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

import Data.Nat as N
import Data.Integer as Z
  
open import Data.Bool 
open import Data.Maybe
open import Data.List as List using (List)

open import Data.Product

open import UNDEFINED

-- Note that hom is what I call foldGroup elsewhere!

-- This is the mathematical definition of group homomorphism. This is mostly
-- annoying to prove because one can't write the blackboard definition directly
-- (since bags are not freely generated).
homIsAnHom : ∀ {T} {{oT : Ord T}} G f (b₁ b₂ : Bag T) → let open AbelianGroup G in
  hom G f (union b₁ b₂) ≡ hom G f b₁ ∙ hom G f b₂
homIsAnHom {{oT}} G f (b⁺₁ , b⁻₁) (b⁺₂ , b⁻₂) =
  begin
    hom G f (union (b⁺₁ , b⁻₁) (b⁺₂ , b⁻₂))
  ≡⟨⟩
    hom G f (uunion b⁺₁ b⁺₂ , uunion b⁻₁ b⁻₂)
  -- TODO: Lots of straightforward group manipulation
  ≡⟨ reveal UNDEFINED ⟩
     hom G f (b⁺₁ , b⁻₁) ∙ hom G f (b⁺₂ , b⁻₂)
  ∎
   where
     open AbelianGroup G
     open ≡-Reasoning
     open import Data.List.Properties
     open import experimental.Sorting

     open Sort ord hiding (insert; toList)

-- Simplest possible definition of the derivative of hom (in the semantic domain).

homDelta : ∀ {T} {{oT : Ord T}} → (G : AbelianGroup L.zero L.zero) → let U = AbelianGroup.Carrier G in (T → U) → Bag T → ΔBag T → U
homDelta G f b db = hom G f db

-- This states that the derivative

homDeltaCorrect : ∀ G f b db → let open AbelianGroup G in
  hom G f (union b db) ≡ hom G f b ∙ homDelta G f b db
homDeltaCorrect G f b db =
  begin
    hom G f (union b db)
  ≡⟨  homIsAnHom G f b db  ⟩
    hom G f b ∙ hom G f db
  ≡⟨⟩
    hom G f b ∙ homDelta G f b db
  ∎
  where
    open AbelianGroup G
    open ≡-Reasoning
    open import Data.List.Properties

--postulate BagGroup :  ∀ {T} (oT : Ord T) → AbelianGroup L.zero L.zero

map₁ : ∀ {A B} {oA : Ord A} {oB : Ord B} → (A → B) → Bag A → Bag B
map₁ f = hom BagGroup (singleton ∘ f)

flatMap : ∀ {A B} {oA : Ord A} {oB : Ord B} → (A → Bag B) → Bag A → Bag B
flatMap f = hom BagGroup f

-- Use instance arguments for Ord.

filter : ∀ {A} {oA : Ord A} → (A → Bool) → Bag A → Bag A
filter p b = hom BagGroup (λ el → if (p el) then (singleton el) else empty) b

{-
TODOs:

 * Express basic functions using hom:
   remove 
   ...

 * State and prove the main theorems. Define changes on bags (as bags first?),
   then the derivative of hom, then write the correctness theorem.

-}

{-
postulate Bag : Set → Set

hom : let B =  AbelianGroup.Carrier G in ∀ {A} → (A → B) → Bag A → B
hom = {!!}
-}


-- Whoops², that's hard to implement. Let's just postulate it.
--map₀ = {!T.map!}

-- map : ({k : Key} → Value k → Value k) → Tree → Tree
-- map f (tree t) = tree $ Indexed.map f t

-- _∈?_ : Key → Tree → Bool
-- k ∈? t = maybeToBool (lookup k t)

------------------------------------------------
-- Elimination forms for trees
------------------------------------------------

-- -- Naive implementations of union.

-- unionWith : (∀ {k} → Value k → Value k → Value k) →
--             -- Left → right → result.
--             Tree → Tree → Tree

-- union : Tree → Tree → Tree
-- union = unionWith const

-- unionsWith : (∀ {k} → Value k → Value k → Value k) → List Tree → Tree

-- -- Left-biased.

-- unions : List Tree → Tree
-- unions = unionsWith const

