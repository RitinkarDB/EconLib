import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

universe u v

/--
A static economic model with:
- a type of agents
- an action space for each agent
-/
structure EconModel where
  Agent : Type u
  Action : Agent → Type v

namespace EconModel

variable (M : EconModel)

/-- A profile assigns an action to each agent. -/
abbrev Profile : Type _ := (i : M.Agent) → M.Action i

section Deviation

variable [DecidableEq M.Agent]

/-- Replace agent `i`'s action in profile `σ` by `x`. -/
def deviate (σ : M.Profile) (i : M.Agent) (x : M.Action i) : M.Profile :=
  Function.update σ i x

@[simp] theorem deviate_self
    (σ : M.Profile) (i : M.Agent) (x : M.Action i) :
    M.deviate σ i x i = x := by
  simp [deviate]

@[simp] theorem deviate_ne
    (σ : M.Profile) {i j : M.Agent} (h : j ≠ i) (x : M.Action i) :
    M.deviate σ i x j = σ j := by
  simp [deviate, h]

@[simp] theorem deviate_idem
    (σ : M.Profile) (i : M.Agent) :
    M.deviate σ i (σ i) = σ := by
  funext j
  by_cases h : j = i
  · subst h
    simp [deviate]
  · simp [deviate, h]

end Deviation

end EconModel
