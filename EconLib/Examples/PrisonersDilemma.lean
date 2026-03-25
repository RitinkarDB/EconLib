import EconLib.GameTheory

inductive PDPlayer
  | row
  | col
deriving DecidableEq

inductive PDAction
  | cooperate
  | defect
deriving DecidableEq

open PDPlayer PDAction

def PDUtility : ((i : PDPlayer) → PDAction) → PDPlayer → ℝ
  | σ, row =>
      match σ row, σ col with
      | cooperate, cooperate => 3
      | cooperate, defect    => 0
      | defect,    cooperate => 5
      | defect,    defect    => 1
  | σ, col =>
      match σ row, σ col with
      | cooperate, cooperate => 3
      | cooperate, defect    => 5
      | defect,    cooperate => 0
      | defect,    defect    => 1

def PD : UtilityModel where
  Agent := PDPlayer
  Action := fun _ => PDAction
  utility := PDUtility

instance : DecidableEq PD.Agent := by
  change DecidableEq PDPlayer
  infer_instance

def defectDefect : PD.Profile :=
  fun
  | row => defect
  | col => defect

theorem defectDefect_is_pureNash :
    PD.IsPureNash defectDefect := by
  intro i x
  cases i <;> cases x <;>
    simp [defectDefect, PD, PDUtility,
      UtilityModel.deviate, EconModel.deviate]

theorem defectDefect_is_equilibrium :
    PD.IsEquilibrium PD.unconstrainedFeasible defectDefect := by
  rw [PD.isEquilibrium_unconstrained_iff_isPureNash]
  exact defectDefect_is_pureNash
