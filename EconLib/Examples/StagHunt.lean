import EconLib.GameTheory.Basic
import Mathlib

inductive SHPlayer
  | row
  | col
deriving DecidableEq

inductive SHAction
  | stag
  | hare
deriving DecidableEq

open SHPlayer SHAction

def SHUtility : ((i : SHPlayer) → SHAction) → SHPlayer → ℝ
  | σ, row =>
      match σ row, σ col with
      | stag, stag => 4
      | stag, hare => 0
      | hare, stag => 3
      | hare, hare => 3
  | σ, col =>
      match σ row, σ col with
      | stag, stag => 4
      | stag, hare => 3
      | hare, stag => 0
      | hare, hare => 3

def SH : UtilityModel where
  Agent := SHPlayer
  Action := fun _ => SHAction
  utility := SHUtility

instance : DecidableEq SH.Agent := by
  change DecidableEq SHPlayer
  infer_instance

def stagStag : SH.Profile :=
  fun
  | row => stag
  | col => stag

def hareHare : SH.Profile :=
  fun
  | row => hare
  | col => hare

theorem stagStag_is_pureNash :
    SH.IsPureNash stagStag := by
  intro i x
  cases i <;> cases x <;>
    simp [stagStag, SH, SHUtility,
      UtilityModel.deviate, EconModel.deviate] <;>
    linarith

theorem hareHare_is_pureNash :
    SH.IsPureNash hareHare := by
  intro i x
  cases i <;> cases x <;>
    simp [hareHare, SH, SHUtility,
      UtilityModel.deviate, EconModel.deviate]

theorem stagStag_is_equilibrium :
    SH.IsEquilibrium SH.unconstrainedFeasible stagStag := by
  rw [SH.isEquilibrium_unconstrained_iff_isPureNash]
  exact stagStag_is_pureNash

theorem hareHare_is_equilibrium :
    SH.IsEquilibrium SH.unconstrainedFeasible hareHare := by
  rw [SH.isEquilibrium_unconstrained_iff_isPureNash]
  exact hareHare_is_pureNash
