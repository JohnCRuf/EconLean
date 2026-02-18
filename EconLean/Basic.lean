/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Basic Definitions

This file contains basic definitions for the EconLean library, including
preference relations, rational preferences, and utility representation.

## Main definitions

* `EconLean.Indifferent` — indifference relation derived from a preorder
* `EconLean.RationalPreference` — a complete preorder (rational preference relation)
* `EconLean.UtilityRepresentation` — a utility function representing a preference relation

## Design notes

We use `Preorder` rather than `PartialOrder` because economic indifference does not
imply equality — two distinct bundles can be equally preferred. A rational preference
is a `Preorder` with completeness (`IsTotal`), not a `LinearOrder` (which requires
antisymmetry).
-/

namespace EconLean

/-! ## Indifference -/

/-- Two alternatives are indifferent if each is weakly preferred to the other. -/
def Indifferent {X : Type*} [Preorder X] (x y : X) : Prop := x ≤ y ∧ y ≤ x

-- Use Unicode tilde operator (U+223C) to avoid conflict with ASCII ~
scoped notation:50 x " ∼ " y => Indifferent x y

variable {X : Type*} [Preorder X]

theorem Indifferent.refl (x : X) : x ∼ x :=
  ⟨le_refl x, le_refl x⟩

theorem Indifferent.symm {x y : X} (h : x ∼ y) : y ∼ x :=
  ⟨h.2, h.1⟩

theorem Indifferent.trans {x y z : X} (hxy : x ∼ y) (hyz : y ∼ z) : x ∼ z :=
  ⟨le_trans hxy.1 hyz.1, le_trans hyz.2 hxy.2⟩

theorem indifferent_equivalence : Equivalence (@Indifferent X _) :=
  ⟨Indifferent.refl, Indifferent.symm, Indifferent.trans⟩

/-! ## Rational Preference -/

/-- A rational preference is a complete preorder: a preorder where any two
alternatives are comparable. This captures the economic notion of rationality
as having complete and transitive preferences. -/
class RationalPreference (X : Type*) extends Preorder X where
  complete : ∀ (x y : X), x ≤ y ∨ y ≤ x

instance {X : Type*} [RationalPreference X] : Std.Total (α := X) (· ≤ ·) :=
  ⟨RationalPreference.complete⟩

/-- Construct a `RationalPreference` from an existing `Preorder` and `Std.Total` instance. -/
def RationalPreference.ofTotalPreorder (X : Type*) [inst : Preorder X]
    [h : Std.Total (α := X) (· ≤ ·)] : RationalPreference X :=
  { inst with complete := h.total }

/-- Preference trichotomy: for any two alternatives in a rational preference,
exactly one of `x < y`, `x ∼ y`, or `y < x` holds. -/
theorem preference_trichotomy {X : Type*} [RationalPreference X] (x y : X) :
    (x < y ∧ ¬(x ∼ y) ∧ ¬(y < x)) ∨
    ((x ∼ y) ∧ ¬(x < y) ∧ ¬(y < x)) ∨
    (y < x ∧ ¬(x ∼ y) ∧ ¬(x < y)) := by
  by_cases hxy : x ≤ y
  · by_cases hyx : y ≤ x
    · right; left
      refine ⟨⟨hxy, hyx⟩, ?_, ?_⟩
      · exact fun h => lt_irrefl _ (lt_of_lt_of_le h hyx)
      · exact fun h => lt_irrefl _ (lt_of_lt_of_le h hxy)
    · left
      refine ⟨lt_of_le_not_ge hxy hyx, ?_, ?_⟩
      · exact fun ⟨_, h⟩ => hyx h
      · exact fun h => hyx (le_of_lt h)
  · have hyx : y ≤ x := (RationalPreference.complete y x).resolve_right hxy
    right; right
    refine ⟨lt_of_le_not_ge hyx (fun h => hxy h), ?_, ?_⟩
    · exact fun ⟨h, _⟩ => hxy h
    · exact fun h => hxy (le_of_lt h)

/-! ## Utility Representation -/

/-- A utility representation of a preference relation is a real-valued function
that preserves the preference ordering. -/
structure UtilityRepresentation (X : Type*) [Preorder X] where
  /-- The utility function. -/
  u : X → ℝ
  /-- The utility function represents the preference: `x ≤ y ↔ u x ≤ u y`. -/
  represents : ∀ (x y : X), x ≤ y ↔ u x ≤ u y

/-- A utility representation preserves strict preference. -/
theorem UtilityRepresentation.represents_strict {X : Type*} [Preorder X]
    (ur : UtilityRepresentation X) (x y : X) : x < y ↔ ur.u x < ur.u y := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  constructor
  · intro ⟨hxy, hyx⟩
    exact ⟨(ur.represents x y).mp hxy, fun h => hyx ((ur.represents y x).mpr h)⟩
  · intro ⟨hxy, hyx⟩
    exact ⟨(ur.represents x y).mpr hxy, fun h => hyx ((ur.represents y x).mp h)⟩

/-- A utility representation maps indifferent alternatives to equal utilities. -/
theorem UtilityRepresentation.represents_indifferent {X : Type*} [Preorder X]
    (ur : UtilityRepresentation X) (x y : X) : (x ∼ y) ↔ ur.u x = ur.u y := by
  constructor
  · intro ⟨hxy, hyx⟩
    exact le_antisymm ((ur.represents x y).mp hxy) ((ur.represents y x).mp hyx)
  · intro h
    exact ⟨(ur.represents x y).mpr (le_of_eq h), (ur.represents y x).mpr (le_of_eq h.symm)⟩

/-- A preference relation with a utility representation is rational (complete). -/
def UtilityRepresentation.toRationalPreference {X : Type*} [Preorder X]
    (ur : UtilityRepresentation X) : RationalPreference X :=
  { ‹Preorder X› with
    complete := fun x y => by
      rcases le_total (ur.u x) (ur.u y) with h | h
      · exact Or.inl ((ur.represents x y).mpr h)
      · exact Or.inr ((ur.represents y x).mpr h) }

/-- Predicate asserting that a function is a utility representation. -/
def IsUtilityRepresentation {X : Type*} [Preorder X] (u : X → ℝ) : Prop :=
  ∀ (x y : X), x ≤ y ↔ u x ≤ u y

/-- A type has a utility representation if there exists a representing function. -/
def HasUtilityRepresentation (X : Type*) [Preorder X] : Prop :=
  ∃ u : X → ℝ, IsUtilityRepresentation u

end EconLean
