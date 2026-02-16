# EconLean

A Lean 4 library for formalizing economic theory, starting with game theory.

## Overview

EconLean provides formal definitions and proofs for fundamental concepts in economic theory. The initial release focuses on game theory, including:

- **Basic Definitions**: Players, strategies, payoffs, and strategy profiles
- **Normal Form Games**: Strategic form games with support for dominant strategies
- **Nash Equilibrium**: Definitions and theorems about Nash equilibrium and related solution concepts
- **Examples**: Classic games like the Prisoner's Dilemma with formal proofs

## Installation

### Prerequisites

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager:
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Clone this repository:
   ```bash
   git clone https://github.com/JohnCRuf/EconLean.git
   cd EconLean
   ```

3. Build the project:
   ```bash
   lake build
   ```

## Usage

### Importing the Library

To use EconLean in your Lean project, add it as a dependency in your `lakefile.lean`:

```lean
require econlean from git
  "https://github.com/JohnCRuf/EconLean.git"
```

Then import the modules you need:

```lean
import EconLean.GameTheory.Basic
import EconLean.GameTheory.NormalForm
import EconLean.GameTheory.Nash
```

### Example: Defining a Game

```lean
import EconLean.GameTheory

-- Define a simple 2x2 game
def myGame : NormalFormGame 2 where
  strategies := fun _ => Bool  -- Each player has two strategies
  payoff := fun profile i => 
    match profile 0, profile 1, i with
    | true, true, _ => 3
    | true, false, 0 => 0
    | true, false, 1 => 5
    | false, true, 0 => 5
    | false, true, 1 => 0
    | false, false, _ => 1
```

### Example: Prisoner's Dilemma

See `EconLean/GameTheory/Examples/PrisonersDilemma.lean` for a complete formalization of the Prisoner's Dilemma, including proofs that:
- Defecting is a strictly dominant strategy for both players
- The (Defect, Defect) profile is a Nash equilibrium

## Project Structure

```
EconLean/
├── EconLean/
│   ├── GameTheory/
│   │   ├── Basic.lean           # Fundamental definitions
│   │   ├── NormalForm.lean      # Normal form games
│   │   ├── Nash.lean            # Nash equilibrium
│   │   └── Examples/
│   │       └── PrisonersDilemma.lean
│   ├── GameTheory.lean          # Main game theory module
│   └── EconLean.lean            # Library entry point
├── Main.lean                     # Executable entry point
├── lakefile.lean                 # Build configuration
└── lean-toolchain                # Lean version specification
```

## Development

### Building

```bash
lake build
```

### Running the Example

```bash
lake exe econlean
```

### Cleaning Build Artifacts

```bash
lake clean
```

## Contributing

Contributions are welcome! Areas for future development include:

- Extensive form games
- Mixed strategy Nash equilibria
- Repeated games
- Auction theory
- Matching theory
- General equilibrium theory

## References

- Osborne, M. (2004). *An Introduction to Game Theory*. Oxford University Press.
- Nash, J. (1950). "Equilibrium points in n-person games". *Proceedings of the National Academy of Sciences*, 36(1), 48-49.

## License

This project is licensed under the Apache 2.0 License.
