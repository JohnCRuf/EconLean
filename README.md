# EconLean

A Lean 4 library for formalizing economic theory, starting with game theory.

## Getting Started

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) and the Lake build tool

### Building the Library

```bash
lake build
```

### Running the Example

```bash
lake exe econlean
```

## Project Structure

```
EconLean/
├── EconLean/                    # Library source files
│   ├── Basic.lean               # Basic definitions
│   ├── GameTheory.lean          # Game theory module
│   ├── GameTheory/              # Game theory submodules
│   │   └── Basic.lean           # Basic game theory definitions
│   ├── GeneralEquilibrium.lean  # General equilibrium theory module
│   └── GeneralEquilibrium/      # General equilibrium submodules
│       └── Basic.lean           # Basic general equilibrium definitions
├── EconLean.lean                # Main library entry point
├── Main.lean                    # Executable entry point
├── lakefile.lean                # Lake build configuration
└── lean-toolchain               # Lean version specification
```

## Library Organization

The library is organized into major branches of economic theory:

- **Game Theory**: Formalization of game-theoretic concepts including players, strategies, payoffs, and equilibrium concepts
- **General Equilibrium Theory**: Formalization of general equilibrium models including agents, production, markets, and equilibrium conditions

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is released under the Apache 2.0 license.

