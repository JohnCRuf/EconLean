/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite Normal-Form Games

A **finite normal-form game** (strategic-form game) consists of:
- A finite set of players
- A finite nonempty set of pure strategies for each player
- A real-valued payoff function for each player over pure strategy profiles

This is the fundamental object of non-cooperative game theory.

## Main definitions

* `FiniteGame n` — an n-player finite normal-form game with players indexed by `Fin n`
* `FiniteGame.PureProfile G` — a pure strategy profile for game `G`
  (a simultaneous choice of one pure strategy per player)

## Design notes

We index players by `Fin n` to make the finite player set explicit. The strategy
types are abstract (`Strategy i : Type*`) rather than concrete (`Fin m`) to allow
natural formulations. Finiteness is stored as a field rather than a typeclass to
avoid universe issues with dependent typeclass synthesis.
-/

namespace EconLean.GameTheory

/-- A finite n-player normal-form game.

Players are indexed by `Fin n`. Each player `i` has:
- A finite type `Strategy i` of pure strategies (must be nonempty)
- A payoff function `payoff i s` giving player `i`'s payoff at pure strategy profile `s`
-/
structure FiniteGame (n : ℕ) where
  /-- The pure strategy type for player `i : Fin n`. -/
  Strategy : Fin n → Type*
  /-- Each player has finitely many pure strategies. -/
  fintype_strat : ∀ i, Fintype (Strategy i)
  /-- Each player has at least one pure strategy (strategy sets are nonempty). -/
  nonempty_strat : ∀ i, Nonempty (Strategy i)
  /-- The payoff function: `payoff i s` is player `i`'s payoff at pure profile `s`. -/
  payoff : ∀ i : Fin n, (∀ j, Strategy j) → ℝ

/-! ### Global typeclass instances derived from the game structure

These instances make the finiteness and nonemptiness of strategy sets available
to Lean's instance synthesis throughout the library. -/

/-- Each player's strategy set is a `Fintype` (derived from the game structure). -/
instance instFintypeStrategy {n : ℕ} (G : FiniteGame n) (i : Fin n) :
    Fintype (G.Strategy i) :=
  G.fintype_strat i

/-- Each player's strategy set is `Nonempty` (derived from the game structure). -/
instance instNonemptyStrategy {n : ℕ} (G : FiniteGame n) (i : Fin n) :
    Nonempty (G.Strategy i) :=
  G.nonempty_strat i

namespace FiniteGame

variable {n : ℕ} (G : FiniteGame n)

/-- A pure strategy profile: a simultaneous choice of one pure strategy per player.
This is the domain of the payoff functions. -/
def PureProfile : Type* := ∀ i : Fin n, G.Strategy i

/-- The space of pure strategy profiles is finite (product of finite sets). -/
noncomputable instance instFintypePureProfile : Fintype G.PureProfile :=
  Pi.instFintype

/-- The space of pure strategy profiles is nonempty (product of nonempty sets). -/
instance instNonemptyPureProfile : Nonempty G.PureProfile :=
  Pi.instNonempty

/-- Player `i`'s payoff at a pure strategy profile, stated as a function of the profile. -/
def payoffAt (i : Fin n) : G.PureProfile → ℝ := G.payoff i
-- `i` is intentionally bound here even though it's implicit in the result type

end FiniteGame

end EconLean.GameTheory
