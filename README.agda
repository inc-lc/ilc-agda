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
-- of Agda, the Agda standard library (version 0.7), generate Everything.agda
-- with the attached Haskell helper, and finally run Agda on this file.
--
-- Given a Unix-like environment (including Cygwin), running the ./agdaCheck.sh
-- script and following instructions given on output will eventually generate
-- Everything.agda and proceed to type check everything on command line.
--
-- We use Agda HEAD from September 2013; Agda 2.3.2.1 might happen to work, but
-- has some bugs with serialization of code using some recent syntactic sugar
-- which we use (https://code.google.com/p/agda/issues/detail?id=756), so it
-- might work or not. When it does not, removing Agda caches (.agdai files)
-- appears to often help. You can use "find . -name '*.agdai' | xargs rm" to do
-- that.
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

import Postulate.Extensionality

import Base.Data.DependentList

-- Variables and contexts
import Base.Syntax.Context

-- Sets of variables
import Base.Syntax.Vars

import Base.Denotation.Notation

-- Environments
import Base.Denotation.Environment

-- Change contexts
import Base.Change.Context

-- # Base, parametric proof.
--
-- This is for a parametric calculus where:
-- types are parametric in base types
-- terms are parametric in constants
--
--
-- Modules are ordered and grouped according to what they represent.

-- ## Definitions

import Parametric.Syntax.Type
import Parametric.Syntax.Term

import Parametric.Denotation.Value
import Parametric.Denotation.Evaluation

import Parametric.Change.Type
import Parametric.Change.Term

import Parametric.Change.Derive

import Parametric.Change.Value
import Parametric.Change.Evaluation

-- ## Proofs

import Parametric.Change.Validity
import Parametric.Change.Specification
import Parametric.Change.Implementation
import Parametric.Change.Correctness

-- # Nehemiah plugin
--
-- The structure is the same as the parametric proof (down to the
-- order and the grouping of modules), except for the postulate module.

-- Postulate an abstract data type for integer Bags.
import Postulate.Bag-Nehemiah

-- ## Definitions
import Nehemiah.Syntax.Type
import Nehemiah.Syntax.Term

import Nehemiah.Denotation.Value
import Nehemiah.Denotation.Evaluation

import Nehemiah.Change.Term
import Nehemiah.Change.Type

import Nehemiah.Change.Derive

import Nehemiah.Change.Value
import Nehemiah.Change.Evaluation

-- ## Proofs

import Nehemiah.Change.Validity
import Nehemiah.Change.Specification
import Nehemiah.Change.Implementation
import Nehemiah.Change.Correctness
