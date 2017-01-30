------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Incrementalization as term-to-term transformation with the Nehemiah plugin.
------------------------------------------------------------------------

module Nehemiah.Change.Derive where

open import Nehemiah.Syntax.Type
open import Nehemiah.Syntax.Term
open import Nehemiah.Change.Type
open import Nehemiah.Change.Term

open import Data.Integer

import Parametric.Change.Derive Const ΔBase as Derive

derive-const : Derive.Structure
derive-const (intlit-const n) = intlit (+ 0)
derive-const add-const        = absV 4 (λ s ds t dt → add ds dt)
derive-const minus-const      = absV 2 (λ t dt → minus dt)
derive-const empty-const      = empty
derive-const insert-const     = absV 4 (λ s ds t dt →
  insert (s ⊕₍ int ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ insert s t)
derive-const union-const      = absV 4 (λ s ds t dt → union ds dt)
derive-const negate-const     = absV 2 (λ t dt → negate dt)
derive-const flatmap-const    = absV 4 (λ s ds t dt →
  flatmap (s ⊕₍ int ⇒ bag ₎ ds) (t ⊕₍ bag ₎ dt) ⊝ flatmap s t)
derive-const sum-const        = absV 2 (λ t dt → sum dt)
derive-const pair-const       = absV 4 (λ a da b db → pair da db)
derive-const fst-const        = absV 2 (λ p dp → fst dp)
derive-const snd-const        = absV 2 (λ p dp → snd dp)

open Derive.Structure derive-const public
