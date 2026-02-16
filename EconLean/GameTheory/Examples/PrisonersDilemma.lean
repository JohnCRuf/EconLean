/-
Copyright (c) 2024 EconLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: EconLean Contributors
-/

import EconLean.GameTheory.Nash

/-!
# Prisoner's Dilemma

A classic example of a game with a dominant strategy equilibrium that is not Pareto optimal.

## The Game

Two prisoners are interrogated separately. Each can either Cooperate (stay silent) 
or Defect (betray the other). The payoffs are structured such that:
* If both cooperate: each gets -1 (1 year in prison)
* If one defects while other cooperates: defector gets 0 (freed), cooperator gets -3 (3 years)
* If both defect: each gets -2 (2 years in prison)

## Main results

* `defectDominatesCooperate`: Defecting is a strictly dominant strategy for both players
* `both_defect_is_nash`: The strategy profile where both defect is a Nash equilibrium
-/

namespace GameTheory.Examples

/-- The two strategies in Prisoner's Dilemma -/
inductive PDStrategy
  | cooperate : PDStrategy
  | defect : PDStrategy
  deriving DecidableEq

open PDStrategy

/-- The Prisoner's Dilemma as a 2-player normal form game -/
def prisonersDilemma : NormalFormGame 2 where
  strategies := fun _ => PDStrategy
  payoff := fun profile i => 
    match profile 0, profile 1, i with
    | cooperate, cooperate, _ => -1  -- Both cooperate: -1 each
    | cooperate, defect, 0 => -3     -- Player 0 cooperates, Player 1 defects: Player 0 gets -3
    | cooperate, defect, 1 => 0      -- Player 0 cooperates, Player 1 defects: Player 1 gets 0
    | defect, cooperate, 0 => 0      -- Player 0 defects, Player 1 cooperates: Player 0 gets 0
    | defect, cooperate, 1 => -3     -- Player 0 defects, Player 1 cooperates: Player 1 gets -3
    | defect, defect, _ => -2        -- Both defect: -2 each

/-- The strategy profile where both players defect -/
def bothDefect : StrategyProfile 2 prisonersDilemma.strategies :=
  fun _ => defect

/-- The strategy profile where both players cooperate -/
def bothCooperate : StrategyProfile 2 prisonersDilemma.strategies :=
  fun _ => cooperate

/-- Defecting strictly dominates cooperating for player 0 in Prisoner's Dilemma -/
theorem defect_dominates_cooperate_p0 : 
    prisonersDilemma.strictlyDominates 0 defect cooperate := by
  intro profile
  unfold NormalFormGame.getPayoff NormalFormGame.profileExcept
  simp
  cases profile 1 with
  | cooperate => norm_num
  | defect => norm_num

/-- Defecting strictly dominates cooperating for player 1 in Prisoner's Dilemma -/
theorem defect_dominates_cooperate_p1 : 
    prisonersDilemma.strictlyDominates 1 defect cooperate := by
  intro profile
  unfold NormalFormGame.getPayoff NormalFormGame.profileExcept
  simp
  cases profile 0 with
  | cooperate => norm_num
  | defect => norm_num

/-- Both defect is a dominant strategy equilibrium -/
theorem both_defect_is_dominant_strategy_equilibrium :
    prisonersDilemma.isDominantStrategyEquilibrium bothDefect := by
  intro i
  left
  unfold NormalFormGame.isStrictlyDominant
  intro s' h
  match i with
  | 0 => 
    cases s' with
    | cooperate => exact defect_dominates_cooperate_p0
    | defect => contradiction
  | 1 =>
    cases s' with
    | cooperate => exact defect_dominates_cooperate_p1
    | defect => contradiction

/-- Both defect is a Nash equilibrium -/
theorem both_defect_is_nash : 
    prisonersDilemma.isNashEquilibrium bothDefect := by
  apply NormalFormGame.dominantStrategyEquilibrium_is_nashEquilibrium
  exact both_defect_is_dominant_strategy_equilibrium

end GameTheory.Examples
