/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Topology.Order.Compact
import EconLean.GameTheory.ExpectedPayoff

/-!
# Best Responses and Nash Equilibrium

## Best Response Correspondence

Given a finite game `G` and a mixed strategy profile `σ`, the **best response set**
for player `i` is the set of mixed strategies for player `i` that maximize their
expected payoff, holding others' strategies fixed.

## Nash Equilibrium

A **Nash equilibrium** is a mixed strategy profile where every player is
playing a best response to the others' strategies.

## Main definitions

* `FiniteGame.pureStratPayoff` — payoff from deviating to a pure strategy
* `FiniteGame.bestResponse` — best response correspondence
* `FiniteGame.IsNashEquilibrium` — Nash equilibrium condition

## Main results

* `FiniteGame.bestResponse_nonempty` — best response sets are nonempty (EVT)
* `FiniteGame.continuous_expectedPayoff_player` — payoff is continuous in one player's strategy
* `FiniteGame.isNashEquilibrium_iff_bestResponse` — NE iff best response for all players
-/

open scoped BigOperators
open Classical

namespace EconLean.GameTheory

variable {n : ℕ} (G : FiniteGame n)

namespace FiniteGame

/-- The expected payoff to player `i` from playing pure strategy `a`,
when other players play according to mixed profile `σ`.

This is `G.expectedPayoff i` when player `i`'s strategy is replaced by
the Dirac delta (vertex) at pure strategy `a`. -/
noncomputable def pureStratPayoff (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) : ℝ :=
  G.expectedPayoff i (Function.update σ i
    ⟨Pi.single a 1, single_mem_stdSimplex ℝ a⟩)

/-- The best response set for player `i` given others play profile `σ`:
the set of mixed strategies that maximize player `i`'s expected payoff. -/
def bestResponse (i : Fin n) (σ : G.MixedProfile) : Set (G.MixedStrategy i) :=
  {τ | ∀ ρ : G.MixedStrategy i,
    G.expectedPayoff i (Function.update σ i τ) ≥
    G.expectedPayoff i (Function.update σ i ρ)}

/-- The expected payoff is continuous in player `i`'s strategy, holding others fixed. -/
theorem continuous_expectedPayoff_player (i : Fin n) (σ : G.MixedProfile) :
    Continuous (fun τ : G.MixedStrategy i =>
      G.expectedPayoff i (Function.update σ i τ)) := by
  apply (G.continuous_expectedPayoff i).comp
  apply continuous_pi
  intro j
  rcases Decidable.em (j = i) with rfl | hne
  · simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hne]
    exact continuous_const

/-- **Best response sets are nonempty** (Extreme Value Theorem).

The expected payoff function is continuous on the compact nonempty simplex
`G.MixedStrategy i`, so it attains its maximum value. -/
theorem bestResponse_nonempty (i : Fin n) (σ : G.MixedProfile) :
    (G.bestResponse i σ).Nonempty := by
  obtain ⟨τ, _, hτ⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty)
    (G.continuous_expectedPayoff_player i σ).continuousOn
  exact ⟨τ, fun ρ => hτ (Set.mem_univ ρ)⟩

/-! ## Nash Equilibrium -/

/-- A **Nash equilibrium** is a mixed strategy profile `σ` such that no player
can profitably deviate by unilaterally changing their strategy. -/
def IsNashEquilibrium (σ : G.MixedProfile) : Prop :=
  ∀ i : Fin n, ∀ τ : G.MixedStrategy i,
    G.expectedPayoff i σ ≥ G.expectedPayoff i (Function.update σ i τ)

/-- `σ` is a Nash equilibrium iff every player's strategy is in their best response set. -/
theorem isNashEquilibrium_iff_bestResponse (σ : G.MixedProfile) :
    G.IsNashEquilibrium σ ↔ ∀ i : Fin n, σ i ∈ G.bestResponse i σ := by
  have hupd : ∀ i : Fin n, Function.update σ i (σ i) = σ := by
    intro i; funext j
    rcases Decidable.em (j = i) with rfl | hne
    · simp
    · simp [Function.update_of_ne hne]
  constructor
  · intro h i ρ
    simp only [IsNashEquilibrium, ge_iff_le] at h
    have key := h i ρ
    simp only [bestResponse, Set.mem_setOf_eq, ge_iff_le]
    calc G.expectedPayoff i (Function.update σ i ρ)
        ≤ G.expectedPayoff i σ := key
      _ = G.expectedPayoff i (Function.update σ i (σ i)) := by rw [hupd i]
  · intro h i τ
    simp only [bestResponse, Set.mem_setOf_eq, ge_iff_le] at h
    have key := h i τ
    simp only [IsNashEquilibrium, ge_iff_le]
    have : G.expectedPayoff i (Function.update σ i (σ i)) = G.expectedPayoff i σ := by
      rw [hupd i]
    linarith

end FiniteGame

end EconLean.GameTheory
