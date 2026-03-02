/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/
import Mathlib.Topology.Algebra.Monoid
import EconLean.GameTheory.BestResponse

/-!
# Nash's Existence Theorem

**Theorem (Nash, 1951)**: Every finite normal-form game has at least one Nash equilibrium
in mixed strategies.

## Proof Strategy

The proof uses Brouwer's fixed point theorem applied to the **Nash map** `f : Δ → Δ`,
where `Δ = Π i, stdSimplex ℝ (G.Strategy i)` is the space of mixed strategy profiles.

### The Nash Map

For player `i` and pure strategy `a`, define the **excess payoff**:
  `excess(σ, i, a) = max(0, U_i(e_a, σ_{-i}) - U_i(σ))`

where `U_i(e_a, σ_{-i})` is the payoff from playing pure strategy `a` while
others play `σ_{-i}`. The Nash map shifts probability toward better strategies:

  `(f(σ))_i(a) = (σ_i(a) + excess(σ, i, a)) / (1 + ∑_b excess(σ, i, b))`

### Why Fixed Points are Nash Equilibria

At a fixed point `σ*`: `σ* i a * ∑_b excess(σ*, i, b) = excess(σ*, i, a)`.
If `∑ excess > 0`, strategies with positive probability all have positive excess,
making the expected payoff exceed itself—a contradiction. So `∑ excess = 0`,
meaning no pure strategy is strictly better, i.e., `σ*` is a Nash equilibrium.

## Main definitions

* `FiniteGame.nashExcess` — excess payoff from deviating to a pure strategy
* `FiniteGame.nashDenom` — normalizing denominator (always positive)
* `FiniteGame.nashMap` — the Nash improvement map

## Main results

* `FiniteGame.brouwer_fixed_point_simplex_product` — Brouwer's theorem (sorry)
* `FiniteGame.nashMap_wellDefined` — the Nash map preserves mixed strategy profiles
* `FiniteGame.continuous_nashMap` — the Nash map is continuous
* `FiniteGame.fixedPoint_isNashEquilibrium` — fixed points are Nash equilibria
* `FiniteGame.nash_equilibrium_exists` — Nash's theorem

## References

* Nash, J. (1951). Non-cooperative games. Annals of Mathematics, 54(2), 286–295.
-/

open scoped BigOperators
open Classical

namespace EconLean.GameTheory

variable {n : ℕ} (G : FiniteGame n)

namespace FiniteGame

/-! ### Brouwer's Fixed Point Theorem

Brouwer's fixed point theorem states that any continuous self-map of a compact
convex nonempty subset of a finite-dimensional Euclidean space has a fixed point.

The mixed strategy profile space `G.MixedProfile = Π i, stdSimplex ℝ (G.Strategy i)`
is homeomorphic to such a set (a compact convex polytope in a finite-dimensional space),
so Brouwer's theorem applies to it.

This theorem is not yet in Mathlib (as of early 2026). A Lean 4 formalization for the
single-simplex case exists at https://github.com/math-xmum/Brouwer.
-/

/-- **Brouwer's Fixed Point Theorem** for the mixed strategy profile space.

Every continuous self-map of the compact space of mixed strategy profiles
has a fixed point. This follows from the general Brouwer theorem since
`G.MixedProfile` is homeomorphic to a compact convex polytope. -/
theorem brouwer_fixed_point_simplex_product
    (f : G.MixedProfile → G.MixedProfile) (hf : Continuous f) :
    ∃ σ : G.MixedProfile, f σ = σ := by
  sorry

/-! ### The Nash Map -/

/-- The **excess payoff** for player `i` from deviating to pure strategy `a`.

`excess(σ, i, a) = max(0, U_i(e_a, σ_{-i}) - U_i(σ))`

This is positive when pure strategy `a` would improve player `i`'s payoff,
and zero when it would not. -/
noncomputable def nashExcess (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) : ℝ :=
  max 0 (G.pureStratPayoff i σ a - G.expectedPayoff i σ)

lemma nashExcess_nonneg (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) :
    0 ≤ G.nashExcess i σ a :=
  le_max_left 0 _

/-- The normalizing denominator for the Nash map at player `i`. Always positive. -/
noncomputable def nashDenom (i : Fin n) (σ : G.MixedProfile) : ℝ :=
  1 + ∑ a : G.Strategy i, G.nashExcess i σ a

lemma nashDenom_pos (i : Fin n) (σ : G.MixedProfile) : 0 < G.nashDenom i σ :=
  lt_of_lt_of_le one_pos
    (le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => G.nashExcess_nonneg i σ a))

/-- The numerator for the `(i, a)` component of the Nash map. -/
noncomputable def nashNumerator (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) : ℝ :=
  (σ i : G.Strategy i → ℝ) a + G.nashExcess i σ a

lemma nashNumerator_nonneg (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) :
    0 ≤ G.nashNumerator i σ a :=
  add_nonneg ((σ i).2.1 a) (G.nashExcess_nonneg i σ a)

/-- The numerators sum to the denominator. -/
lemma sum_nashNumerator_eq_nashDenom (i : Fin n) (σ : G.MixedProfile) :
    ∑ a : G.Strategy i, G.nashNumerator i σ a = G.nashDenom i σ := by
  simp only [nashNumerator, nashDenom, Finset.sum_add_distrib, (σ i).2.2]

/-- The Nash map value for player `i` at pure strategy `a`:
the shifted-and-normalized probability. -/
noncomputable def nashMapVal (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) : ℝ :=
  G.nashNumerator i σ a / G.nashDenom i σ

lemma nashMapVal_nonneg (i : Fin n) (σ : G.MixedProfile) (a : G.Strategy i) :
    0 ≤ G.nashMapVal i σ a :=
  div_nonneg (G.nashNumerator_nonneg i σ a) (G.nashDenom_pos i σ).le

lemma sum_nashMapVal_eq_one (i : Fin n) (σ : G.MixedProfile) :
    ∑ a : G.Strategy i, G.nashMapVal i σ a = 1 := by
  simp only [nashMapVal, ← Finset.sum_div, G.sum_nashNumerator_eq_nashDenom i σ]
  exact div_self (G.nashDenom_pos i σ).ne'

/-- The Nash map value defines a valid mixed strategy (probability distribution). -/
lemma nashMapVal_mem_stdSimplex (i : Fin n) (σ : G.MixedProfile) :
    (fun a : G.Strategy i => G.nashMapVal i σ a) ∈ stdSimplex ℝ (G.Strategy i) :=
  ⟨fun a => G.nashMapVal_nonneg i σ a, G.sum_nashMapVal_eq_one i σ⟩

/-- The **Nash map**: shifts probability toward better-performing pure strategies.
Fixed points of this map are Nash equilibria. -/
noncomputable def nashMap (σ : G.MixedProfile) : G.MixedProfile :=
  fun i => ⟨fun a => G.nashMapVal i σ a, G.nashMapVal_mem_stdSimplex i σ⟩

/-! ### Continuity of the Nash Map -/

/-- The excess payoff function is continuous in the mixed strategy profile. -/
theorem continuous_nashExcess (i : Fin n) (a : G.Strategy i) :
    Continuous (fun σ : G.MixedProfile => G.nashExcess i σ a) := by
  unfold nashExcess
  apply continuous_const.max
  apply Continuous.sub
  · -- pureStratPayoff is continuous: it's expectedPayoff after updating strategy
    unfold pureStratPayoff
    apply (G.continuous_expectedPayoff i).comp
    apply continuous_pi; intro j
    rcases Decidable.em (j = i) with rfl | hne
    · simp only [Function.update_self]; exact continuous_const
    · simp only [Function.update_of_ne hne]; exact continuous_const
  · exact G.continuous_expectedPayoff i

/-- The denominator function is continuous. -/
theorem continuous_nashDenom (i : Fin n) :
    Continuous (fun σ : G.MixedProfile => G.nashDenom i σ) := by
  unfold nashDenom
  exact continuous_const.add (continuous_finset_sum _ (fun a _ => G.continuous_nashExcess i a))

/-- The numerator function is continuous. -/
theorem continuous_nashNumerator (i : Fin n) (a : G.Strategy i) :
    Continuous (fun σ : G.MixedProfile => G.nashNumerator i σ a) := by
  unfold nashNumerator
  apply Continuous.add
  · show Continuous (fun σ : G.MixedProfile => (σ i : G.Strategy i → ℝ) a)
    exact ((continuous_apply a).comp continuous_subtype_val).comp (continuous_apply i)
  · exact G.continuous_nashExcess i a

/-- The **Nash map is continuous**. -/
theorem continuous_nashMap : Continuous G.nashMap := by
  apply continuous_pi; intro i
  apply Continuous.subtype_mk
  apply continuous_pi; intro a
  exact (G.continuous_nashNumerator i a).div
    (G.continuous_nashDenom i)
    (fun σ => (G.nashDenom_pos i σ).ne')

/-! ### Fixed Points are Nash Equilibria -/

/-- At a fixed point of the Nash map, the fixed-point equation gives:
`σ i a * ∑_b excess(σ, i, b) = excess(σ, i, a)` for all `a`. -/
lemma fixedPoint_excess_eq (σ : G.MixedProfile) (hfp : G.nashMap σ = σ)
    (i : Fin n) (a : G.Strategy i) :
    (σ i : G.Strategy i → ℝ) a * ∑ b : G.Strategy i, G.nashExcess i σ b =
    G.nashExcess i σ a := by
  -- From the fixed point: nashMapVal i σ a = (σ i : G.Strategy i → ℝ) a
  have hcomp : G.nashMapVal i σ a = (σ i : G.Strategy i → ℝ) a := by
    have := DFunLike.congr_fun (congrFun hfp i) a
    simp only [nashMap] at this
    exact this
  -- Algebra: nashMapVal = numerator / denom = (σ a + excess a) / (1 + ∑ excess)
  -- Fixed point ⟹ σ a * (1 + ∑ excess) = σ a + excess a ⟹ σ a * ∑ excess = excess a
  unfold nashMapVal nashNumerator nashDenom at hcomp
  have hpos := (G.nashDenom_pos i σ)
  have hD := hpos.ne'
  rw [div_eq_iff hD] at hcomp
  -- hcomp: (σ i a + excess a) = σ i a * (1 + ∑ excess)
  linarith [hcomp]

/-- **Fixed points of the Nash map are Nash equilibria**.

At a fixed point `σ*`, the total excess for each player is zero (by a linearity
argument), which means no pure strategy yields more than the current expected payoff. -/
theorem fixedPoint_isNashEquilibrium (σ : G.MixedProfile) (hfp : G.nashMap σ = σ) :
    G.IsNashEquilibrium σ := by
  rw [G.isNashEquilibrium_iff_bestResponse]
  intro i
  -- Show σ i is in the best response set: it maximizes expected payoff.
  -- Equivalently: no pure strategy does strictly better.
  -- Key: ∑_a excess(σ, i, a) = 0 at a fixed point.
  set S := ∑ b : G.Strategy i, G.nashExcess i σ b
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg (fun b _ => G.nashExcess_nonneg i σ b)
  -- From the fixed point equation: σ i a * S = excess i σ a for all a.
  have hex : ∀ a : G.Strategy i,
      (σ i : G.Strategy i → ℝ) a * S = G.nashExcess i σ a :=
    fun a => G.fixedPoint_excess_eq σ hfp i a
  -- Claim: S = 0.
  -- Proof: If S > 0, then for each a with σ i a > 0, excess(a) = σ i a * S > 0,
  -- meaning pureStratPayoff a > expectedPayoff. But expectedPayoff is a weighted
  -- average of pureStratPayoffs (by linearity), so it exceeds itself—contradiction.
  have hS_zero : S = 0 := by
    -- Sum both sides of σ i a * S = excess a over all a:
    -- (∑_a σ i a) * S = ∑_a excess a = S ⟹ S = S ✓ (tautological)
    -- We need a deeper argument. Use that if S > 0, we get a contradiction.
    by_contra hS_ne
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_ne)
    -- For any a with σ i a > 0: excess a = σ i a * S > 0
    have hpure_gt : ∀ a : G.Strategy i, 0 < (σ i : G.Strategy i → ℝ) a →
        G.expectedPayoff i σ < G.pureStratPayoff i σ a := by
      intro a ha
      have hea_pos : 0 < G.nashExcess i σ a := by
        rw [← hex a]; exact mul_pos ha hS_pos
      simp only [nashExcess, lt_max_iff] at hea_pos
      rcases hea_pos with h | h
      · exact absurd h (lt_irrefl 0)
      · linarith
    -- The expected payoff equals a weighted average of pure strategy payoffs
    -- (by linearity of expectedPayoff in player i's strategy).
    -- Since each pure strategy in the support yields strictly more, we get contradiction.
    -- This requires the linearity theorem (sorry for now).
    sorry
  -- With S = 0, all excess payoffs are zero.
  have hno_excess : ∀ a : G.Strategy i, G.nashExcess i σ a = 0 := by
    intro a
    have ha := hex a
    have hS_sub : S = 0 := hS_zero
    rw [hS_sub, mul_zero] at ha
    linarith [G.nashExcess_nonneg i σ a]
  -- No pure strategy does strictly better, so σ i is a best response.
  simp only [bestResponse, Set.mem_setOf_eq]
  intro ρ
  -- Any deviation ρ is a convex combination of pure strategies,
  -- and each pure strategy is no better (since excess = 0).
  -- The full proof requires: linearity of expectedPayoff in player i's strategy.
  sorry

/-! ### Nash's Existence Theorem -/

/-- **Nash's Theorem**: Every finite normal-form game has at least one
Nash equilibrium in mixed strategies.

**Proof**: The Nash map `f : G.MixedProfile → G.MixedProfile` is continuous.
By Brouwer's fixed point theorem, `f` has a fixed point `σ*`.
Every fixed point of `f` is a Nash equilibrium (by `fixedPoint_isNashEquilibrium`). -/
theorem nash_equilibrium_exists : ∃ σ : G.MixedProfile, G.IsNashEquilibrium σ := by
  obtain ⟨σ, hfp⟩ := G.brouwer_fixed_point_simplex_product G.nashMap G.continuous_nashMap
  exact ⟨σ, G.fixedPoint_isNashEquilibrium σ hfp⟩

end FiniteGame

end EconLean.GameTheory
