import EconLib.GameTheory.Basic

namespace UtilityModel

variable (M : UtilityModel)
variable [DecidableEq M.Agent]

/--
At profile `σ`, player `i`'s current action weakly dominates all unilateral alternatives.
This is a profile-relative dominance notion.
-/
def ActionWeaklyDominatesAt
    (σ : M.Profile) (i : M.Agent) : Prop :=
  ∀ x : M.Action i,
    M.utility σ i ≥ M.utility (M.deviate σ i x) i

/--
At profile `σ`, player `i`'s current action strictly dominates all distinct unilateral alternatives.
-/
def ActionStrictlyDominatesAt
    (σ : M.Profile) (i : M.Agent) : Prop :=
  ∀ x : M.Action i, x ≠ σ i →
    M.utility σ i > M.utility (M.deviate σ i x) i

theorem actionWeaklyDominatesAt_of_actionStrictlyDominatesAt
    (σ : M.Profile)
    (i : M.Agent)
    (h : M.ActionStrictlyDominatesAt σ i) :
    M.ActionWeaklyDominatesAt σ i := by
  intro x
  by_cases hx : x = σ i
  · subst hx
    simp [UtilityModel.deviate, EconModel.deviate]
  · exact le_of_lt (h x hx)

/--
If every player's current action weakly dominates all unilateral alternatives
at the given profile, then the profile is a pure Nash equilibrium.
-/
theorem isPureNash_of_actionWeaklyDominatesAt
    (σ : M.Profile)
    (h : ∀ i : M.Agent, M.ActionWeaklyDominatesAt σ i) :
    M.IsPureNash σ := by
  intro i x
  exact h i x

/--
Hence, under unconstrained feasibility, the profile is also an equilibrium
in the abstract sense.
-/
theorem isEquilibrium_of_actionWeaklyDominatesAt
    (σ : M.Profile)
    (h : ∀ i : M.Agent, M.ActionWeaklyDominatesAt σ i) :
    M.IsEquilibrium M.unconstrainedFeasible σ := by
  rw [M.isEquilibrium_unconstrained_iff_isPureNash]
  exact M.isPureNash_of_actionWeaklyDominatesAt σ h

theorem isPureNash_of_actionStrictlyDominatesAt
    (σ : M.Profile)
    (h : ∀ i : M.Agent, M.ActionStrictlyDominatesAt σ i) :
    M.IsPureNash σ := by
  intro i x
  by_cases hx : x = σ i
  · subst hx
    simp [UtilityModel.deviate, EconModel.deviate]
  · exact le_of_lt (h i x hx)

theorem isEquilibrium_of_actionStrictlyDominatesAt
    (σ : M.Profile)
    (h : ∀ i : M.Agent, M.ActionStrictlyDominatesAt σ i) :
    M.IsEquilibrium M.unconstrainedFeasible σ := by
  rw [M.isEquilibrium_unconstrained_iff_isPureNash]
  exact M.isPureNash_of_actionStrictlyDominatesAt σ h

end UtilityModel
