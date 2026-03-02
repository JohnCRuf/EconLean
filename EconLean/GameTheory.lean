/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/

/-!
# Game Theory

This module contains definitions and theorems related to non-cooperative game theory.

## Main Definitions

* `EconLean.GameTheory.FiniteGame` — a finite n-player normal-form game
* `EconLean.GameTheory.FiniteGame.MixedProfile` — mixed strategy profiles
* `EconLean.GameTheory.FiniteGame.expectedPayoff` — expected payoff under mixed strategies
* `EconLean.GameTheory.FiniteGame.IsNashEquilibrium` — Nash equilibrium condition

## Main Theorems

* `EconLean.GameTheory.FiniteGame.nash_equilibrium_exists` — Nash's existence theorem:
  every finite game has at least one Nash equilibrium in mixed strategies

## References

* Nash, J. (1950). Equilibrium points in n-person games. PNAS, 36(1), 48–49.
* Nash, J. (1951). Non-cooperative games. Annals of Mathematics, 54(2), 286–295.
-/

import EconLean.GameTheory.Basic
