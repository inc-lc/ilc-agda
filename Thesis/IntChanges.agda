module Thesis.IntChanges where

open import Data.Integer.Base
open import Relation.Binary.PropositionalEquality

open import Thesis.Changes
open import Theorem.Groups-Nehemiah

private
  intCh = ℤ
instance
  intCS : ChangeStructure ℤ
intCS = record
  { Ch = ℤ
  ; ch_from_to_ = λ dv v1 v2 → v1 + dv ≡ v2
  ; isCompChangeStructure = record
    { isChangeStructure = record
      { _⊕_ = _+_
      ; fromto→⊕ = λ dv v1 v2 v2≡v1+dv → v2≡v1+dv
      ; _⊝_ = _-_
      ; ⊝-fromto = λ a b → n+[m-n]=m {a} {b}
      }
    ; _⊚_ = λ da1 da2 → da1 + da2
    ; ⊚-fromto = i⊚-fromto
    }
  }
  where
    i⊚-fromto : (a1 a2 a3 : ℤ) (da1 da2 : intCh) →
      a1 + da1 ≡ a2 → a2 + da2 ≡ a3 → a1 + (da1 + da2) ≡ a3
    i⊚-fromto a1 a2 a3 da1 da2 a1+da1≡a2 a2+da2≡a3
      rewrite sym (associative-int a1 da1 da2) | a1+da1≡a2 = a2+da2≡a3
