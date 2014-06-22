------------------------------------------------------------------------
-- INCREMENTAL λ-CALCULUS
--
-- Machine-checked formalization of the theoretical results presented
-- in the paper:
--
--   Yufei Cai, Paolo G. Giarrusso, Tillmann Rendel, Klaus Ostermann.
--   A Theory of Changes for Higher-Order Languages:
--   Incrementalizing λ-Calculi by Static Differentiation.
--   To appear at PLDI, ACM 2014.
--
-- We claim that this formalization
--
--   (1) proves every lemma and theorem in Sec. 2 and 3 of the paper,
--   (2) formally specifies the interface between our incrementalization
--       framework and potential plugins, and
--   (3) shows that the plugin interface can be instantiated.
--
-- The first claim is the main reason for a machine-checked
-- proof: We want to be sure that we got the proofs right.
--
-- The second claim is about reusability and applicability: Only
-- a clearly defined interface allows other researchers to
-- provide plugins for our framework.
--
-- The third claim is to show that the plugin interface is
-- consistent: An inconsistent plugin interface would allow to
-- prove arbitrary results in the framework.
------------------------------------------------------------------------

module README where

-- We know two good ways to read this code base. You can either
-- use Emacs with agda2-mode to interact with the source files,
-- or you can use a web browser to view the pretty-printed and
-- hyperlinked source files. For Agda power users, we also
-- include basic setup information for your own machine.


-- IF YOU WANT TO USE A BROWSER
-- ============================
--
-- Start with *HTML* version of this readme. On the AEC
-- submission website (online or inside the VM), follow the link
-- "view the Agda code in their browser" to the file
-- agda/README.html.
--
-- The source code is syntax highlighted and hyperlinked. You can
-- click on module names to open the corresponding files, or you
-- can click on identifiers to jump to their definition. In
-- general, a Agda file with name `Foo/Bar/Baz.agda` contains a
-- module `Foo.Bar.Baz` and is shown in an HTML file
-- `Foo.Bar.Baz.html`.
--
-- Note that we also include the HTML files generated for our
-- transitive dependencies from the Agda standard library. This
-- allows you to follow hyperlinks to the Agda standard
-- library. It is the default behavior of `agda --html` which we
-- used to generate the HTML.
--
-- To get started, continue below on "Where to start reading?".



-- IF YOU WANT TO USE EMACS
-- ========================
--
-- Open this file in Emacs with agda2-mode installed. See below
-- for which Agda version you need to install. On the VM image,
-- everything is setup for you and you can just open this file in
-- Emacs.
--
--   C-c C-l   Load code. Type checks and syntax highlights. Use
--             this if the code is not syntax highlighted, or
--             after you changed something that you want to type
--             check.
--
--   M-.       Jump to definition of identifier at the point.
--   M-*       Jump back.
--
-- Note that README.agda imports Everything.agda which imports
-- every Agda file in our formalization. So if README.agda type
-- checks successfully, everything does. If you want to type
-- check everything from scratch, delete the *.agdai files to
-- disable separate compilation. You can use "find . -name
-- '*.agdai' | xargs rm" to do that.
--
-- More information on the Agda mode is available on the Agda wiki:
--
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.QuickGuideToEditingTypeCheckingAndCompilingAgdaCode
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.EmacsModeKeyCombinations
--
-- To get started, continue below on "Where to start reading?".



-- IF YOU WANT TO USE YOUR OWN SETUP
-- =================================
--
-- To typecheck this formalization, you need to install the appropriate version
-- of Agda (2.4.0), the Agda standard library (version 0.8), generate
-- Everything.agda with the attached Haskell helper, and finally run Agda on
-- this file.
--
-- Given a Unix-like environment (including Cygwin), running the ./agdaCheck.sh
-- script and following instructions given on output will eventually generate
-- Everything.agda and proceed to type check everything on command line.
--
-- If you're not an Agda power user, it is probably easier to use
-- the VM image or look at the pretty-printed and hyperlinked
-- HTML files, see above.



-- WHERE TO START READING?
-- =======================
--
-- modules.pdf
--   The graph of dependencies between Agda modules.
--   Good if you want to get a broad overview.
--
-- README.agda
--   This file. A coarse-grained introduction to the Agda
--   formalization.  Good if you want to begin at the beginning
--   and understand the structure of our code.
--
-- PLDI14-List-of-Theorems.agda
--   Pointers to the Agda formalizations of all theorems, lemmas
--   or definitions in the PLDI paper. Good if you want to read
--   the paper and the Agda code side by side.
--
--   Here is an import of this file, so you can jump to it
--   directly (use M-. in Emacs or click the module name in the
--   Browser):

import PLDI14-List-of-Theorems

-- Everything.agda
--   Imports every Agda module in our formalization. Good if you
--   want to make sure you don't miss anything.
--
--   Again, here's is an import of this file so you can navigate
--   there:

import Everything

-- (This import is also important to ensure that if we typecheck
-- README.agda, we also typecheck every other file of our
-- formalization).



-- THE AGDA CODE
-- =============
--
-- The formalization has four parts:
--
--   1. A formalization of change structures. This lives in
--   Base.Change.Algebra. (What we call "change structure" in the
--   paper, we call "change algebra" in the Agda code. We changed
--   the name when writing the paper, and never got around to
--   updating the name in the Agda code).
--
--   2. Incrementalization framework for first-class functions,
--   with extension points for plugging in data types and their
--   incrementalization. This lives in the Parametric.*
--   hierarchy.
--
--   3. An example plugin that provides integers and bags
--   with negative multiplicity. This lives in the Nehemiah.*
--   hierarchy. (For some reason, we choose to call this
--   particular incarnation of the plugin Nehemiah).
--
--   4. Other material that is unrelated to the framework/plugin
--   distinction. This is all other files.



-- FORMALIZATION OF CHANGE STRUCTURES
-- ==================================
--
-- Section 2 of the paper, and Base.Change.Algebra in Agda.

import Base.Change.Algebra



-- INCREMENTALIZATION FRAMEWORK
-- ============================
--
-- Section 3 of the paper, and Parametric.* hierarchy in Agda.
--
-- The extension points are implemented as module parameters. See
-- detailed explanation in Parametric.Syntax.Type and
-- Parametric.Syntax.Term. Some extension points are for types,
-- some for values, and some for proof fragments. In Agda, these
-- three kinds of entities are unified anyway, so we can encode
-- all of them as module parameters.
--
-- Every module in the Parametric.* hierarchy adds at least one
-- extension point, so the module hierarchy of a plugin will
-- typically mirror the Parametric.* hierarchy, defining the
-- values for these extension points.
--
-- Firstly, we have the syntax of types and terms, the erased
-- change structure for function types and incrementalization as
-- a term-to-term transformation. The contents of these modules
-- formalizes Sec. 3.1 and 3.2 of the paper, except for the
-- second and third line of Figure 3, which is formalized further
-- below.

import Parametric.Syntax.Type   -- syntax of types
import Parametric.Syntax.Term   -- syntax of terms
import Parametric.Change.Type   -- simply-typed changes
import Parametric.Change.Derive -- incrementalization

-- Secondly, we define the usual denotational semantics of the
-- simply-typed lambda calculus in terms of total functions, and
-- the change semantics in terms of a change structure on total
-- functions. The contents of these modules formalize Sec. 3.3,
-- 3.4 and 3.5 of the paper.

import Parametric.Denotation.Value      -- standard values
import Parametric.Denotation.Evaluation -- standard evaluation
import Parametric.Change.Validity       -- dependently-typed changes
import Parametric.Change.Specification  -- change evaluation

-- Thirdly, we define terms that operate on simply-typed changes,
-- and connect them to their values. The concents of these
-- modules formalize the second and third line of Figure 3, as
-- well as the semantics of these lines.

import Parametric.Change.Term        -- terms that operate on simply-typed changes
import Parametric.Change.Value       -- the values of these terms
import Parametric.Change.Evaluation  -- connecting the terms and their values

-- Finally, we prove correctness by connecting the (syntactic)
-- incrementalization to the (semantic) change evaluation by a
-- logical relation, and a proof that the values of terms
-- produced by the incrementalization transformation are related
-- to the change values of the original terms. The contents of
-- these modules formalize Sec. 3.6.

import Parametric.Change.Implementation -- logical relation
import Parametric.Change.Correctness    -- main correctness proof



-- EXAMPLE PLUGIN
-- ==============
--
-- Sec. 3.7 in the paper, and the Nehemiah.* hierarchy in Agda.
--
-- The module structure of the plugin follows the structure of
-- the Parametric.* hierarchy.  For example, the extension point
-- defined in Parametric.Syntax.Term is instantiated in
-- Nehemiah.Syntax.Term.
--
-- As discussed in Sec. 3.7 of the paper, the point of this
-- plugin is not to speed up any real programs, but to show "that
-- the interface for proof plugins can be implemented". As a
-- first step towards proving correctness of the more complicated
-- plugin with integers, bags and finite maps we implement in
-- Scala, we choose to define plugin with integers and bags in
-- Agda. Instead of implementing bags (with negative
-- multiplicities, like in the paper) in Agda, though, we
-- postulate that a group of such bags exist. Note that integer
-- bags with integer multiplicities are actually the free group
-- given a singleton operation `Integer -> Bag`, so this should
-- be easy to formalize in principle.

-- Before we start with the plugin, we postulate an abstract data
-- type for integer bags.
import Postulate.Bag-Nehemiah

-- Firstly, we extend the syntax of types and terms, the erased
-- change structure for function types, and incrementalization as
-- a term-to-term transformation to account for the data types of
-- the Nehemiah language. The contents of these modules
-- instantiate the extension points in Sec. 3.1 and 3.2 of the
-- paper, except for the second and third line of Figure 3, which
-- is instantiated further below.

import Nehemiah.Syntax.Type
import Nehemiah.Syntax.Term
import Nehemiah.Change.Type
import Nehemiah.Change.Derive

-- Secondly, we extend the usual denotational semantics and the
-- change semantics to account for the data types of the Nehemiah
-- language. The contents of these modules instantiate the
-- extension points in Sec. 3.3, 3.4 and 3.5 of the paper.

import Nehemiah.Denotation.Value
import Nehemiah.Denotation.Evaluation
import Nehemiah.Change.Validity
import Nehemiah.Change.Specification

-- Thirdly, we extend the terms that operate on simply-typed
-- changes, and the connection to their values to account for the
-- data types of the Nehemiah language. The concents of these
-- modules instantiate the extension points in the second and
-- third line of Figure 3.

import Nehemiah.Change.Term
import Nehemiah.Change.Value
import Nehemiah.Change.Evaluation

-- Finally, we extend the logical relation and the main
-- correctness proof to account for the data types in the
-- Nehemiah language. The contents of these modules instantiate
-- the extension points defined in Sec. 3.6.

import Nehemiah.Change.Implementation
import Nehemiah.Change.Correctness



-- OTHER MATERIAL
-- ==============
--
-- We postulate extensionality of Agda functions. This postulate
-- is well known to be compatible with Agda's type theory.

import Postulate.Extensionality

-- For historical reasons, we reexport Data.List.All from the
-- standard library under the name DependentList.

import Base.Data.DependentList

-- This module supports overloading the ⟦_⟧ notation based on
-- Agda's instance arguments.

import Base.Denotation.Notation

-- These modules implement contexts including typed de Bruijn
-- indices to represent bound variables, sets of bound variables,
-- and environments. These modules are parametric in the set of
-- types (that are stored in contexts) and the set of values
-- (that are stored in environments). So these modules are even
-- more parametric than the Parametric.* hierarchy.

import Base.Syntax.Context
import Base.Syntax.Vars
import Base.Denotation.Environment

-- This module contains some helper definitions to merge a
-- context of values and a context of changes.
import Base.Change.Context
