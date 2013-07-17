module Syntax.Language.Base where

-- Language description à la Plotkin (LCF as PL)
--
-- To describe a language, we supply base types and constants.
--
-- Following Plotkin, we use the metavariable L for instances of
-- language descriptions. We call the language description `Base`
-- so that we can write `Base.type` etc.

record Base : Set₁ where
  constructor
    lang
  field
    type  : Set
    const : Set
