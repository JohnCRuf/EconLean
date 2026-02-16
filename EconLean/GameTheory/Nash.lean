/-
Copyright (c) 2024 EconLean Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: EconLean Contributors
-/

import EconLean.GameTheory.NormalForm

/-!
# Nash Equilibrium

This file defines Nash equilibrium and related concepts.

## Main definitions

* `NashEquilibrium`: A strategy profile where each player's strategy is a best response
* `StrictNashEquilibrium`: A Nash equilibrium where each player's strategy is the unique best response
* `dominantStrategyEquilibrium`: An equilibrium where each player plays a dominant strategy

## References
* [Nash1950] J. Nash, "Equilibrium points in n-person games", PNAS, 1950.
* [Osborne2004] M. Osborne, *An Introduction to Game Theory*, Oxford University Press, 2004.
-/

namespace GameTheory

namespace NormalFormGame

variable {n : ℕ} (G : NormalFormGame n)

/-- A Nash equilibrium is a strategy profile where each player's strategy 
    is a best response to the other players' strategies -/
def isNashEquilibrium (profile : StrategyProfile n G.strategies) : Prop :=
  ∀ (i : Fin n), G.isBestResponse i profile (profile i)

/-- A strict Nash equilibrium is a Nash equilibrium where each player's strategy
    is the unique best response -/
def isStrictNashEquilibrium (profile : StrategyProfile n G.strategies) : Prop :=
  ∀ (i : Fin n) (s' : G.strategies i), 
    s' ≠ profile i → 
    G.getPayoff i profile > G.getPayoff i (G.profileExcept i profile s')

/-- A dominant strategy equilibrium is a strategy profile where each player
    plays a dominant strategy -/
def isDominantStrategyEquilibrium (profile : StrategyProfile n G.strategies) : Prop :=
  ∀ (i : Fin n), G.isStrictlyDominant i (profile i) ∨ G.isWeaklyDominant i (profile i)

/-- Every strict Nash equilibrium is a Nash equilibrium -/
theorem strictNashEquilibrium_is_nashEquilibrium 
    (profile : StrategyProfile n G.strategies) :
    G.isStrictNashEquilibrium profile → G.isNashEquilibrium profile := by
  intro h_strict i
  unfold isBestResponse
  intro s'
  by_cases h : s' = profile i
  · rw [h]
  · unfold isStrictNashEquilibrium at h_strict
    have := h_strict i s' h
    linarith

/-- Every dominant strategy equilibrium is a Nash equilibrium -/
theorem dominantStrategyEquilibrium_is_nashEquilibrium
    (profile : StrategyProfile n G.strategies) :
    G.isDominantStrategyEquilibrium profile → G.isNashEquilibrium profile := by
  intro h_dom i
  unfold isBestResponse
  intro s'
  unfold isDominantStrategyEquilibrium at h_dom
  cases h_dom i with
  | inl h_strict =>
    by_cases h : s' = profile i
    · rw [h]
    · unfold isStrictlyDominant at h_strict
      have := h_strict s' h
      unfold strictlyDominates at this
      have := this (G.profileExcept i profile s')
      linarith
  | inr h_weak =>
    unfold isWeaklyDominant at h_weak
    by_cases h : s' = profile i
    · rw [h]
    · have := h_weak s' h
      unfold weaklyDominates at this
      have := this.1 (G.profileExcept i profile s')
      exact this

end NormalFormGame

end GameTheory
