import EconLib.Basic

/--
An economic model together with a real-valued utility/payoff representation.
-/
structure UtilityModel extends EconModel where
  utility : EconModel.Profile toEconModel → Agent → ℝ

namespace UtilityModel

variable (M : UtilityModel)

/-- Profiles in the underlying economic model. -/
abbrev Profile : Type _ := EconModel.Profile M.toEconModel

section Deviation

variable [DecidableEq M.Agent]

/-- Reuse unilateral deviation from the underlying economic model. -/
def deviate (σ : M.Profile) (i : M.Agent) (x : M.Action i) : M.Profile :=
  EconModel.deviate M.toEconModel σ i x

@[simp] theorem deviate_self
    (σ : M.Profile) (i : M.Agent) (x : M.Action i) :
    M.deviate σ i x i = x := by
  simp [deviate, EconModel.deviate]

@[simp] theorem deviate_ne
    (σ : M.Profile) {i j : M.Agent} (h : j ≠ i) (x : M.Action i) :
    M.deviate σ i x j = σ j := by
  simp [deviate, EconModel.deviate, h]

/--
`feasible σ i` is the set of actions available to agent `i`
as unilateral deviations from profile `σ`.
-/
abbrev FeasibleDeviation :=
  (σ : M.Profile) → (i : M.Agent) → Set (M.Action i)

/--
A predicate saying whether a profile itself is feasible/admissible.
This is useful in constrained-choice settings.
-/
abbrev ProfileFeasible :=
  M.Profile → Prop

/-- Agent `i` has a profitable feasible deviation from `σ` to `x`. -/
def ProfitableDeviation
    (feasible : M.FeasibleDeviation)
    (σ : M.Profile) (i : M.Agent) (x : M.Action i) : Prop :=
  x ∈ feasible σ i ∧ M.utility (M.deviate σ i x) i > M.utility σ i

/-- Agent `i` is locally optimal at profile `σ`. -/
def IsLocallyOptimal
    (feasible : M.FeasibleDeviation)
    (σ : M.Profile) (i : M.Agent) : Prop :=
  ∀ x : M.Action i,
    x ∈ feasible σ i →
    M.utility σ i ≥ M.utility (M.deviate σ i x) i

/--
A profile is an equilibrium if every agent is locally optimal.
This is the basic no-profitable-feasible-deviation notion.
-/
def IsEquilibrium
    (feasible : M.FeasibleDeviation)
    (σ : M.Profile) : Prop :=
  ∀ i : M.Agent, M.IsLocallyOptimal feasible σ i

/--
A stronger equilibrium notion requiring both:
- the profile itself is feasible
- every agent is locally optimal
-/
def IsFeasibleEquilibrium
    (profileFeasible : M.ProfileFeasible)
    (feasible : M.FeasibleDeviation)
    (σ : M.Profile) : Prop :=
  profileFeasible σ ∧ M.IsEquilibrium feasible σ

theorem isEquilibrium_iff_no_profitable_deviation
    (feasible : M.FeasibleDeviation)
    (σ : M.Profile) :
    M.IsEquilibrium feasible σ ↔
    ∀ i x, ¬ M.ProfitableDeviation feasible σ i x := by
  constructor
  · intro h i x hx
    exact not_lt_of_ge (h i x hx.1) hx.2
  · intro h i x hx
    exact le_of_not_gt (fun hgt => h i x ⟨hx, hgt⟩)

end Deviation

end UtilityModel
