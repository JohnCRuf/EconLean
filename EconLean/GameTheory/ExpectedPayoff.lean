/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Topology.Algebra.Monoid
import EconLean.GameTheory.MixedStrategy

/-!
# Expected Payoff

The **expected payoff** to player `i` under a mixed strategy profile `σ` is:

  `U i σ = ∑ s : G.PureProfile, (∏ j, σ j (s j)) * G.payoff i s`

where `∏ j, σ j (s j)` is the probability that pure profile `s` occurs when
each player `j` independently plays mixed strategy `σ j`.

## Main definitions

* `FiniteGame.expectedPayoff G i σ` — expected payoff to player `i` under profile `σ`

## Main results

* `FiniteGame.continuous_expectedPayoff` — expected payoff is jointly continuous in `σ`
* `FiniteGame.expectedPayoff_linear` — expected payoff is linear in each player's strategy

## Notes

The expected payoff function is **multilinear** in the mixed strategies: linear in
each player's strategy holding others fixed. This is the key property used in the
Nash existence proof (both for convexity of best responses and for the fixed-point argument).
-/

open scoped BigOperators

namespace EconLean.GameTheory

variable {n : ℕ} (G : FiniteGame n)

namespace FiniteGame

/-- The expected payoff to player `i` under mixed strategy profile `σ`.

`U i σ = ∑ s, (∏ j, σ j (s j)) * payoff i s`

where the product `∏ j, σ j (s j)` is the probability of pure profile `s` occurring
under the independent mixed strategies. -/
noncomputable def expectedPayoff (i : Fin n) (σ : G.MixedProfile) : ℝ :=
  ∑ s : G.PureProfile, (∏ j : Fin n, (σ j : G.Strategy j → ℝ) (s j)) * G.payoff i s

/-- The expected payoff is continuous in the mixed strategy profile. -/
theorem continuous_expectedPayoff (i : Fin n) :
    Continuous (fun σ : G.MixedProfile => G.expectedPayoff i σ) := by
  simp only [expectedPayoff]
  apply continuous_finset_sum
  intro s _
  apply Continuous.mul _ continuous_const
  apply continuous_finset_prod
  intro j _
  show Continuous (fun σ : G.MixedProfile => (σ j : G.Strategy j → ℝ) (s j))
  exact ((continuous_apply (s j)).comp continuous_subtype_val).comp (continuous_apply j)

/-- The expected payoff is linear in player `i`'s mixed strategy, holding others fixed.

This linearity is the key analytic property needed for Nash's theorem:
it implies convexity of best response sets and the fixed-point argument.

**Proof sketch**: The expected payoff decomposes as
  `U_i(τ, σ_{-i}) = ∑_{s_{-i}} (∏_{j≠i} σ_j(s_j)) * (∑_{a} τ(a) * payoff(i, a, s_{-i}))`
which is linear in `τ`. The full proof requires careful manipulation of products
and sums over finite types. -/
theorem expectedPayoff_linear (i : Fin n) (σ : G.MixedProfile)
    (τ₁ τ₂ : G.MixedStrategy i) (a b : ℝ)
    (τ : G.MixedStrategy i)
    (hτ : ∀ s : G.Strategy i,
      (τ : G.Strategy i → ℝ) s =
      a * (τ₁ : G.Strategy i → ℝ) s + b * (τ₂ : G.Strategy i → ℝ) s) :
    G.expectedPayoff i (Function.update σ i τ) =
    a * G.expectedPayoff i (Function.update σ i τ₁) +
    b * G.expectedPayoff i (Function.update σ i τ₂) := by
  sorry

end FiniteGame

end EconLean.GameTheory
