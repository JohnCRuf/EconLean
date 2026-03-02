/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Compactness.Compact
import EconLean.GameTheory.FiniteGame

/-!
# Mixed Strategies

A **mixed strategy** for player `i` in a finite game is a probability distribution
over their finite set of pure strategies. We represent this as an element of the
standard probability simplex `stdSimplex ℝ (G.Strategy i)`.

A **mixed strategy profile** assigns one mixed strategy to each player.

## Main definitions

* `FiniteGame.MixedStrategy G i` — the mixed strategy simplex for player `i`
* `FiniteGame.MixedProfile G` — the product of mixed strategy simplices

## Main results

* `FiniteGame.MixedProfile.instCompactSpace` — compact (product of compact spaces)
* `FiniteGame.MixedProfile.instNonempty` — nonempty (each simplex is nonempty)
-/

namespace EconLean.GameTheory

variable {n : ℕ} (G : FiniteGame n)

namespace FiniteGame

/-- The mixed strategy simplex for player `i`: probability distributions
over `G.Strategy i`. Uses `abbrev` so it is definitionally transparent. -/
abbrev MixedStrategy (i : Fin n) : Type* :=
  stdSimplex ℝ (G.Strategy i)

/-- The mixed strategy profile space: one probability distribution per player.
Uses `abbrev` so it is definitionally transparent. -/
abbrev MixedProfile : Type* :=
  ∀ i : Fin n, G.MixedStrategy i

namespace MixedProfile

/-- The mixed strategy profile space has the product topology (inherited). -/
instance instTopologicalSpace : TopologicalSpace G.MixedProfile := inferInstance

/-- The mixed strategy profile space is compact.

Each simplex `stdSimplex ℝ (G.Strategy i)` is compact (closed and bounded in ℝⁿ),
and a product of compact spaces is compact (Tychonoff). -/
instance instCompactSpace : CompactSpace G.MixedProfile := by
  show CompactSpace (∀ i : Fin n, stdSimplex ℝ (G.Strategy i))
  haveI : ∀ i : Fin n, CompactSpace (stdSimplex ℝ (G.Strategy i)) :=
    fun _ => inferInstance
  exact Pi.compactSpace

/-- The mixed strategy profile space is nonempty.

Each `stdSimplex ℝ (G.Strategy i)` is nonempty because `G.Strategy i` is nonempty
(it contains at least one vertex of the simplex). -/
instance instNonempty : Nonempty G.MixedProfile := by
  show Nonempty (∀ i : Fin n, stdSimplex ℝ (G.Strategy i))
  exact inferInstance

/-- Every mixed strategy has nonneg probabilities: `0 ≤ (σ i : G.Strategy i → ℝ) s`. -/
lemma prob_nonneg (σ : G.MixedProfile) (i : Fin n) (s : G.Strategy i) :
    0 ≤ (σ i : G.Strategy i → ℝ) s :=
  (σ i).2.1 s

/-- Mixed strategy probabilities sum to 1: `∑ s, (σ i : G.Strategy i → ℝ) s = 1`. -/
lemma prob_sum_one (σ : G.MixedProfile) (i : Fin n) :
    ∑ s : G.Strategy i, (σ i : G.Strategy i → ℝ) s = 1 :=
  (σ i).2.2

end MixedProfile

end FiniteGame

end EconLean.GameTheory
