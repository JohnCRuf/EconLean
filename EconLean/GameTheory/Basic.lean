/-
Copyright (c) 2026 John C. Ruf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John C. Ruf
-/

/-!
# Basic Game Theory Definitions

This file re-exports all submodules of the `EconLean.GameTheory` module.

## Submodules

* `EconLean.GameTheory.FiniteGame` — finite normal-form games and pure strategy profiles
* `EconLean.GameTheory.MixedStrategy` — mixed strategies and mixed strategy profiles
* `EconLean.GameTheory.ExpectedPayoff` — expected payoff and its continuity
* `EconLean.GameTheory.BestResponse` — best response correspondence and Nash equilibrium
* `EconLean.GameTheory.NashExistence` — Nash's existence theorem
-/

import EconLean.GameTheory.FiniteGame
import EconLean.GameTheory.MixedStrategy
import EconLean.GameTheory.ExpectedPayoff
import EconLean.GameTheory.BestResponse
import EconLean.GameTheory.NashExistence
