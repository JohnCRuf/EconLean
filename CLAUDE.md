# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

EconLean is a Lean 4 library for formalizing economic theory. It uses Lean 4 v4.14.0 with the Lake build system. The project is in early stages — module files exist with placeholder TODOs but no substantial definitions or theorems yet.

## Build Commands

- **Build the library:** `lake build`
- **Run the executable:** `lake exe econlean`

## Architecture

- `EconLean.lean` — root import file; all top-level modules must be imported here
- `EconLean/Basic.lean` — shared basic definitions
- `EconLean/GameTheory.lean` + `EconLean/GameTheory/` — game theory module
- `EconLean/GeneralEquilibrium.lean` + `EconLean/GeneralEquilibrium/` — general equilibrium module
- `Main.lean` — executable entry point (imports the full library)
- `lakefile.lean` — Lake build configuration (package `econlean`, library `EconLean`, executable `econlean`)

## Conventions

- Each `.lean` file starts with a copyright header (Apache 2.0, author John C. Ruf) followed by a module docstring (`/-! ... -/`)
- New modules should follow the existing pattern: a top-level `EconLean/Topic.lean` that re-exports submodules from `EconLean/Topic/`
- New top-level modules must be added to `EconLean.lean`
