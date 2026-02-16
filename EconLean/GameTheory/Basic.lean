/-
Copyright (c) 2024 EconLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: EconLean Contributors
-/

/-!
# Basic Game Theory Definitions

This file contains the fundamental definitions for game theory:
* Players
* Strategies
* Payoffs

## Main definitions

* `Player α`: A type class representing a player in a game
* `Strategy`: A strategy available to a player
* `Payoff`: The payoff or utility received by a player

## References
* [Osborne2004] M. Osborne, *An Introduction to Game Theory*, Oxford University Press, 2004.
-/

namespace GameTheory

/-- A player in a game, represented by a type α -/
def Player (α : Type*) := α

/-- A strategy is an action or decision available to a player -/
def Strategy (α : Type*) := α

/-- A payoff represents the utility or outcome received by a player -/
def Payoff := ℝ

/-- A strategy profile is a tuple of strategies, one for each player -/
def StrategyProfile (n : ℕ) (S : Fin n → Type*) := (i : Fin n) → S i

/-- A payoff function maps strategy profiles to payoffs for each player -/
def PayoffFunction (n : ℕ) (S : Fin n → Type*) := 
  StrategyProfile n S → (i : Fin n) → Payoff

end GameTheory
