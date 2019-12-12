-- # A Reflexive Graph Model of Sized Types

-- This is the formalisation of my M.Sc. thesis, available at

--   https://limperg.de/paper/msc-thesis/

-- I define λST, a simply typed lambda calculus extended with sized types. I
-- then give a reflexive graph model of λST which incorporates a notion of size
-- irrelevance. This document lists all modules belonging to the development,
-- roughly in dependency order.

module index where


-- ## Object Language

-- The following modules define the syntax and type system of λST.

-- Sizes, size contexts, size comparison.
import Source.Size

-- First formulation of size substitutions.
import Source.Size.Substitution.Canonical

-- Second formulation of size substitutions.
import Source.Size.Substitution.Universe

-- An abstraction for things which size substitutions can be applied to.
import Source.Size.Substitution.Theory

-- Types.
import Source.Type

-- Terms.
import Source.Term


-- ## Model

-- The following modules define the reflexive graph model of λST.

-- Propositional reflexive graphs and their morphisms.
import Model.RGraph

-- Model of sizes, size contexts, size comparison.
import Model.Size

-- Families of propositional reflexive graphs (PRGraph families) and their
-- morphisms.
import Model.Type.Core

-- The terminal PRGraph family.
import Model.Terminal

-- Binary products of PRGraph families.
import Model.Product

-- Exponentials of PRGraph families (model of the function space).
import Model.Exponential

-- Model of size quantification.
import Model.Quantification

-- Model of the natural number type.
import Model.Nat

-- Model of the stream type.
import Model.Stream

-- Model of types and type contexts.
import Model.Type

-- Model of terms.
import Model.Term


-- ## Utility Library

-- The following modules contain utility code. The majority of this is an
-- implementation of (parts of) Homotopy Type Theory.

import Util.Data.Product
import Util.HoTT.Equiv
import Util.HoTT.Equiv.Core
import Util.HoTT.Equiv.Induction
import Util.HoTT.FunctionalExtensionality
import Util.HoTT.HLevel
import Util.HoTT.HLevel.Core
import Util.HoTT.Homotopy
import Util.HoTT.Section
import Util.HoTT.Singleton
import Util.HoTT.Univalence
import Util.HoTT.Univalence.Axiom
import Util.HoTT.Univalence.Beta
import Util.HoTT.Univalence.ContrFormulation
import Util.HoTT.Univalence.Statement
import Util.Induction.WellFounded
import Util.Prelude
import Util.Relation.Binary.Closure.SymmetricTransitive
import Util.Relation.Binary.LogicalEquivalence
import Util.Relation.Binary.PropositionalEquality
import Util.Vec


-- ## Miscellaneous

-- Some terms of λST and their typing derivations.
import Source.Examples

-- Experiments with a hypothetical Agda without the ∞ < ∞ rule.
import irreflexive-lt

-- Ordinals as defined in the HoTT book.
import Ordinal.HoTT

-- Plump ordinals as presented by Shulman.
import Ordinal.Shulman
