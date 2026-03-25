import EconLib.Equilibrium

/--
A simple one-agent choice problem:
- a type of choices
- a utility function on choices
- a feasible set of choices
-/
structure ChoiceProblem where
  Choice : Type
  utility : Choice → ℝ
  feasible : Set Choice

namespace ChoiceProblem

variable (C : ChoiceProblem)

/--
A choice is optimal if:
- it is feasible
- every feasible alternative yields weakly lower utility
-/
def IsOptimal (x : C.Choice) : Prop :=
  x ∈ C.feasible ∧ ∀ y, y ∈ C.feasible → C.utility y ≤ C.utility x

/--
The one-agent utility model induced by a choice problem.
A profile is just the unique agent's choice.
-/
def toUtilityModel : UtilityModel where
  Agent := PUnit
  Action := fun _ => C.Choice
  utility := fun σ _ => C.utility (σ PUnit.unit)

instance : DecidableEq (C.toUtilityModel).Agent := by
  change DecidableEq PUnit
  infer_instance

/--
The feasible deviations induced by the feasible set of the choice problem.
-/
def inducedFeasible : (C.toUtilityModel).FeasibleDeviation :=
  fun _ _ => C.feasible

/--
A profile is feasible iff its chosen object lies in the feasible set.
-/
def profileFeasible : (C.toUtilityModel).ProfileFeasible :=
  fun σ => σ PUnit.unit ∈ C.feasible

/--
The profile corresponding to choosing `x`.
-/
def profileOf (x : C.Choice) : (C.toUtilityModel).Profile :=
  fun _ => x

theorem isOptimal_iff_isFeasibleEquilibrium_profileOf
    (x : C.Choice) :
    C.IsOptimal x ↔
      (C.toUtilityModel).IsFeasibleEquilibrium
        C.profileFeasible
        C.inducedFeasible
        (C.profileOf x) := by
  constructor
  · intro hx
    rcases hx with ⟨hx_feas, hx_opt⟩
    constructor
    · simpa [ChoiceProblem.profileFeasible, ChoiceProblem.profileOf] using hx_feas
    · intro _ y hy
      simpa [ChoiceProblem.toUtilityModel, ChoiceProblem.inducedFeasible,
        ChoiceProblem.profileOf, UtilityModel.IsEquilibrium,
        UtilityModel.IsLocallyOptimal, UtilityModel.deviate,
        EconModel.deviate] using hx_opt y hy
  · intro h
    rcases h with ⟨hx_feas, hx_opt⟩
    constructor
    · simpa [ChoiceProblem.profileFeasible, ChoiceProblem.profileOf] using hx_feas
    · intro y hy
      have h₀ := hx_opt PUnit.unit y hy
      simpa [ChoiceProblem.toUtilityModel, ChoiceProblem.inducedFeasible,
        ChoiceProblem.profileOf, UtilityModel.IsEquilibrium,
        UtilityModel.IsLocallyOptimal, UtilityModel.deviate,
        EconModel.deviate] using h₀

end ChoiceProblem
