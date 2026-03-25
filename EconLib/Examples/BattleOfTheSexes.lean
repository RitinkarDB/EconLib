import EconLib.GameTheory.Basic

inductive BoSPlayer
  | row
  | col
deriving DecidableEq

inductive BoSAction
  | ballet
  | football
deriving DecidableEq

open BoSPlayer BoSAction

def BoSUtility : ((i : BoSPlayer) → BoSAction) → BoSPlayer → ℝ
  | σ, row =>
      match σ row, σ col with
      | ballet,   ballet   => 2
      | ballet,   football => 0
      | football, ballet   => 0
      | football, football => 1
  | σ, col =>
      match σ row, σ col with
      | ballet,   ballet   => 1
      | ballet,   football => 0
      | football, ballet   => 0
      | football, football => 2

def BoS : UtilityModel where
  Agent := BoSPlayer
  Action := fun _ => BoSAction
  utility := BoSUtility

instance : DecidableEq BoS.Agent := by
  change DecidableEq BoSPlayer
  infer_instance

def balletBallet : BoS.Profile :=
  fun
  | row => ballet
  | col => ballet

def footballFootball : BoS.Profile :=
  fun
  | row => football
  | col => football

theorem balletBallet_is_pureNash :
    BoS.IsPureNash balletBallet := by
  intro i x
  cases i <;> cases x <;>
    simp [balletBallet, BoS, BoSUtility,
      UtilityModel.deviate, EconModel.deviate]

theorem footballFootball_is_pureNash :
    BoS.IsPureNash footballFootball := by
  intro i x
  cases i <;> cases x <;>
    simp [footballFootball, BoS, BoSUtility,
      UtilityModel.deviate, EconModel.deviate]

theorem balletBallet_is_equilibrium :
    BoS.IsEquilibrium BoS.unconstrainedFeasible balletBallet := by
  rw [BoS.isEquilibrium_unconstrained_iff_isPureNash]
  exact balletBallet_is_pureNash

theorem footballFootball_is_equilibrium :
    BoS.IsEquilibrium BoS.unconstrainedFeasible footballFootball := by
  rw [BoS.isEquilibrium_unconstrained_iff_isPureNash]
  exact footballFootball_is_pureNash
