module Denotational.ExtensionalityPostulate where

-- POSTULATE EXTENSIONALITY

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
postulate ext : Extensionality zero zero
