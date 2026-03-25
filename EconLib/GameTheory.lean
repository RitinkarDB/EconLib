import EconLib.Equilibrium

namespace UtilityModel

variable (M : UtilityModel)
variable [DecidableEq M.Agent]

/-- In the unconstrained case, every unilateral action is feasible. -/
def unconstrainedFeasible : M.FeasibleDeviation :=
  fun _ _ => Set.univ

/-- Pure Nash equilibrium. -/
def IsPureNash (σ : M.Profile) : Prop :=
  ∀ i (x : M.Action i),
    M.utility σ i ≥ M.utility (M.deviate σ i x) i

theorem isLocallyOptimal_unconstrained_iff
    (σ : M.Profile) (i : M.Agent) :
    M.IsLocallyOptimal M.unconstrainedFeasible σ i ↔
    ∀ x : M.Action i,
      M.utility σ i ≥ M.utility (M.deviate σ i x) i := by
  constructor
  · intro h x
    exact h x (by simp [unconstrainedFeasible])
  · intro h x hx
    exact h x

theorem isEquilibrium_unconstrained_iff_isPureNash
    (σ : M.Profile) :
    M.IsEquilibrium M.unconstrainedFeasible σ ↔ M.IsPureNash σ := by
  constructor
  · intro h i x
    exact h i x (by simp [unconstrainedFeasible])
  · intro h i x hx
    exact h i x

end UtilityModel
