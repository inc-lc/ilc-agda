Hacking Guide for the Agda codebase in this directory
=====================================================

Naming conventions
------------------

 * Use fullish words for exported identifiers
   (bad: E, okish: Expr, good: Expression).

 * Use upper-case first letters for types.

 * Use lower-case first letters for not-types.

Module names
------------

 * First component:

     - `Base` means helper definitions that work for
       formalizing programming language meta-theory in general

     - `Parametric` means language formalization that works for
       all simply-typed lambda calculi independent of base types.

     - `⟨language⟩` means formalization of the specific
       language ⟨language⟩.

 * Further components explain what aspect of a language's
   metatheory is formalized. A module `⟨language⟩.⟨Foo⟩` should
   probably be a plugin for a module `Parametric.⟨Foo⟩`. And
   `Base.⟨Foo⟩` should contain widely reusable helper definitions
   for the code in `Parametric.⟨Foo⟩`.

Implicit arguments
------------------

Only use implicit arguments when they can get inferred in most
situations. Some rules of thumb:

 * If the value of an argument in a telescope is fully determined
   by the type of an explicit argument that occurs later in the
   same telescope, make the earlier argument implicit.

 * If the value of an argument in a telescope is fully determined
   by the return type of the telescope, you might want to make
   the argument implicit.
