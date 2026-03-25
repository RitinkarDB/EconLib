import EconLib.GameTheory.Basic
import Mathlib

inductive MPPlayer
  | row
  | col
deriving DecidableEq

inductive MPAction
  | heads
  | tails
deriving DecidableEq

open MPPlayer MPAction

def MPUtility : ((i : MPPlayer) → MPAction) → MPPlayer → ℝ
  | σ, row =>
      match σ row, σ col with
      | heads, heads => 1
      | heads, tails => -1
      | tails, heads => -1
      | tails, tails => 1
  | σ, col =>
      match σ row, σ col with
      | heads, heads => -1
      | heads, tails => 1
      | tails, heads => 1
      | tails, tails => -1

def MP : UtilityModel where
  Agent := MPPlayer
  Action := fun _ => MPAction
  utility := MPUtility

instance : DecidableEq MP.Agent := by
  change DecidableEq MPPlayer
  infer_instance

theorem no_profile_is_pureNash (σ : MP.Profile) :
    ¬ MP.IsPureNash σ := by
  intro h
  cases hrow : σ row <;> cases hcol : σ col
  ·
    have h₁ := h col tails
    simp [MP, MPUtility, hrow, hcol,
      UtilityModel.deviate, EconModel.deviate] at h₁
    linarith
  ·
    have h₁ := h row tails
    simp [MP, MPUtility, hrow, hcol,
      UtilityModel.deviate, EconModel.deviate] at h₁
    linarith
  ·
    have h₁ := h row heads
    simp [MP, MPUtility, hrow, hcol,
      UtilityModel.deviate, EconModel.deviate] at h₁
    linarith
  ·
    have h₁ := h col heads
    simp [MP, MPUtility, hrow, hcol,
      UtilityModel.deviate, EconModel.deviate] at h₁
    linarith

theorem no_profile_is_equilibrium (σ : MP.Profile) :
    ¬ MP.IsEquilibrium MP.unconstrainedFeasible σ := by
  intro h
  rw [MP.isEquilibrium_unconstrained_iff_isPureNash] at h
  exact no_profile_is_pureNash σ h
