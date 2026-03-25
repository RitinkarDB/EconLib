# EconLib

**EconLib** is an experimental Lean 4 library for formal economics.

Its current focus is a reusable framework for **static microeconomic reasoning** based on profiles, feasible unilateral deviations, local optimality, and equilibrium. The longer-run aim is to develop formal infrastructure for economics that can later support richer work in game theory, mechanism design, preference theory, decision theory, social choice, and equilibrium theory.

## Current scope

At present, EconLib provides a small but reusable formal framework for:

- static economic models with agent-indexed action spaces
- profiles of actions
- unilateral deviation
- feasible deviations
- profitable deviation
- local optimality
- equilibrium
- a stronger feasibility-aware equilibrium notion for constrained-choice settings

It also includes:

- a game-theoretic specialisation to **pure Nash equilibrium**
- profile-relative weak and strict dominance results
- a one-agent constrained-choice specialisation
- a collection of canonical examples

## Main idea

A large class of static economic arguments has the same underlying form:

1. fix a profile of actions or choices
2. let one agent consider a feasible unilateral deviation
3. compare the resulting payoff with the current one
4. define stability or optimality by the absence of profitable feasible deviations

EconLib isolates and formalises that pattern.

In unconstrained strategic settings, this yields pure Nash equilibrium.  
In one-agent constrained-choice settings, it yields constrained optimality once profile feasibility is added.

## Implemented modules

### Foundations
- `EconModel`
- profiles
- unilateral deviation
- basic deviation lemmas

### Equilibrium
- feasible deviations
- profitable deviations
- local optimality
- equilibrium
- feasible equilibrium
- characterisations of equilibrium as absence of profitable deviation

### Game theory
- pure Nash equilibrium as the unconstrained special case
- best-response characterisations
- dominance-style sufficient conditions

### Choice
- one-agent choice problems
- induced utility models
- feasible equilibrium as constrained optimality

## Examples

The repository currently includes formalised examples of:

- Prisoner’s Dilemma
- Battle of the Sexes
- Matching Pennies
- Stag Hunt

These examples serve both as tests of the API and as chapter-level demonstrations of the framework.

## Example results

Among the results currently formalised are:

- equilibrium iff no profitable feasible deviation
- feasible equilibrium iff profile feasibility plus no profitable feasible deviation
- pure Nash iff every player is best-responding
- strict dominance implies weak dominance
- weak or strict dominance-style conditions imply equilibrium
- Matching Pennies has no pure-strategy Nash equilibrium
- Battle of the Sexes has exactly two pure-strategy Nash equilibria
- Stag Hunt has exactly two pure-strategy Nash equilibria

## Repository structure

```text
EconLib/
  Foundations/
    Basic.lean
  Equilibrium/
    Basic.lean
  GameTheory/
    Basic.lean
    Dominance.lean
  Choice/
    Basic.lean
  Examples/
    PrisonersDilemma.lean
    BattleOfTheSexes.lean
    MatchingPennies.lean
    StagHunt.lean
```


## Why Lean?

The point of the project is not merely to encode known definitions. It is to make the logical structure of economic arguments explicit and reusable.

Formalisation helps by:

- making hidden assumptions visible
- separating structural results from model-specific content
- allowing generic lemmas to be proved once and reused
- providing a foundation for future automated reasoning tools for economics

## Long-run direction

The present codebase is only the first branch of a larger planned library.

Natural extensions include:

- mechanism design
- preference theory
- utility representation
- von Neumann–Morgenstern expected utility
- subjective expected utility
- non-standard decision theory
- social choice
- general equilibrium
- dynamic and stochastic models

The current static framework is intended as a foundation for those later developments, not as a complete formalisation of economics.

## Building

This is a standard Lean 4 / Lake project.

To build the library:

```bash
lake build
```
## Development Status


This repository is currently tied to a PhD chapter on formalising static microeconomic reasoning in Lean 4. The code should therefore be understood as an actively developing research library rather than a finished general-purpose package.

## Author

Ritinkar Das Bhaumik

## License

This project is licensed under the Apache License 2.0.
See the `LICENSE` file for details.
