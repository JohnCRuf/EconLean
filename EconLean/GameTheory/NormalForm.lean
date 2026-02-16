/-
Copyright (c) 2024 EconLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: EconLean Contributors
-/

import EconLean.GameTheory.Basic

/-!
# Normal Form Games

This file defines normal form (strategic form) games.

## Main definitions

* `NormalFormGame`: A game in normal form with n players
* `bestResponse`: A strategy that maximizes a player's payoff given others' strategies
* `strictlyDominant`: A strategy that is strictly better than all others regardless of opponents' play
* `weaklyDominant`: A strategy that is at least as good as all others regardless of opponents' play

## References
* [Osborne2004] M. Osborne, *An Introduction to Game Theory*, Oxford University Press, 2004.
-/

namespace GameTheory

/-- A normal form game with n players -/
structure NormalFormGame (n : ℕ) where
  /-- The strategy space for each player -/
  strategies : (i : Fin n) → Type*
  /-- The payoff function for the game -/
  payoff : PayoffFunction n strategies

namespace NormalFormGame

variable {n : ℕ} (G : NormalFormGame n)

/-- Get the payoff for player i given a strategy profile -/
def getPayoff (i : Fin n) (profile : StrategyProfile n G.strategies) : Payoff :=
  G.payoff profile i

/-- A strategy profile where all players except i play according to profile -/
def profileExcept (i : Fin n) (profile : StrategyProfile n G.strategies) 
    (s : G.strategies i) : StrategyProfile n G.strategies :=
  fun j => if h : j = i then h ▸ s else profile j

/-- A strategy s is a best response for player i to the strategies of other players -/
def isBestResponse (i : Fin n) (profile : StrategyProfile n G.strategies) 
    (s : G.strategies i) : Prop :=
  ∀ (s' : G.strategies i), 
    G.getPayoff i (G.profileExcept i profile s) ≥ 
    G.getPayoff i (G.profileExcept i profile s')

/-- A strategy s strictly dominates strategy s' for player i -/
def strictlyDominates (i : Fin n) (s s' : G.strategies i) : Prop :=
  ∀ (profile : StrategyProfile n G.strategies),
    G.getPayoff i (G.profileExcept i profile s) > 
    G.getPayoff i (G.profileExcept i profile s')

/-- A strategy s weakly dominates strategy s' for player i -/
def weaklyDominates (i : Fin n) (s s' : G.strategies i) : Prop :=
  (∀ (profile : StrategyProfile n G.strategies),
    G.getPayoff i (G.profileExcept i profile s) ≥ 
    G.getPayoff i (G.profileExcept i profile s')) ∧
  (∃ (profile : StrategyProfile n G.strategies),
    G.getPayoff i (G.profileExcept i profile s) > 
    G.getPayoff i (G.profileExcept i profile s'))

/-- A strategy is strictly dominant if it strictly dominates all other strategies -/
def isStrictlyDominant (i : Fin n) (s : G.strategies i) : Prop :=
  ∀ (s' : G.strategies i), s ≠ s' → G.strictlyDominates i s s'

/-- A strategy is weakly dominant if it weakly dominates all other strategies -/
def isWeaklyDominant (i : Fin n) (s : G.strategies i) : Prop :=
  ∀ (s' : G.strategies i), s ≠ s' → G.weaklyDominates i s s'

end NormalFormGame

end GameTheory
