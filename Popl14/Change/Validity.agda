module Popl14.Change.Validity where

open import Popl14.Syntax.Type
open import Popl14.Denotation.Value

import Parametric.Change.Validity ⟦_⟧Base as Validity

-- Changes for Calculus Popl14

open import Popl14.Change.Type 
open import Popl14.Change.Value
open import Theorem.Groups-Popl14
open import Data.Unit

validity-structure : Validity.Structure
validity-structure = record
    { ΔVal-base = λ ι → ⟦ ΔBase ι ⟧Base
    ; valid-base = λ _ _ → ⊤
    ; apply-ΔVal-base = ⟦apply-base⟧
    ; diff-ΔVal-base = ⟦diff-base⟧
    ; R[v,u-v]-base = tt
    ; v+[u-v]=u-base = λ
        { {base-int} {u} {v} → n+[m-n]=m {v} {u}
        ; {base-bag} {u} {v} → a++[b\\a]=b {v} {u}
        }
    }

open Validity.Structure validity-structure public
