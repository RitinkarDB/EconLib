import EconLib.GameTheory.Basic
import Mathlib

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

def balletFootball : BoS.Profile :=
  fun
  | row => ballet
  | col => football

def footballBallet : BoS.Profile :=
  fun
  | row => football
  | col => ballet

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

theorem balletFootball_not_pureNash :
    ¬ BoS.IsPureNash balletFootball := by
  intro h
  have h₁ := h row football
  simp [balletFootball, BoS, BoSUtility,
    UtilityModel.deviate, EconModel.deviate] at h₁
  linarith

theorem footballBallet_not_pureNash :
    ¬ BoS.IsPureNash footballBallet := by
  intro h
  have h₁ := h row ballet
  simp [footballBallet, BoS, BoSUtility,
    UtilityModel.deviate, EconModel.deviate] at h₁
  linarith

lemma sigma_eq_balletBallet
    (σ : BoS.Profile)
    (hrow : σ row = ballet)
    (hcol : σ col = ballet) :
    σ = balletBallet := by
  funext i
  cases i <;> assumption

lemma sigma_eq_balletFootball
    (σ : BoS.Profile)
    (hrow : σ row = ballet)
    (hcol : σ col = football) :
    σ = balletFootball := by
  funext i
  cases i <;> assumption

lemma sigma_eq_footballBallet
    (σ : BoS.Profile)
    (hrow : σ row = football)
    (hcol : σ col = ballet) :
    σ = footballBallet := by
  funext i
  cases i <;> assumption

lemma sigma_eq_footballFootball
    (σ : BoS.Profile)
    (hrow : σ row = football)
    (hcol : σ col = football) :
    σ = footballFootball := by
  funext i
  cases i <;> assumption

theorem isPureNash_iff
    (σ : BoS.Profile) :
    BoS.IsPureNash σ ↔ σ = balletBallet ∨ σ = footballFootball := by
  cases hrow : σ row <;> cases hcol : σ col
  · constructor
    · intro _
      left
      exact sigma_eq_balletBallet σ hrow hcol
    · intro h
      rcases h with hbb | hff
      · subst hbb
        exact balletBallet_is_pureNash
      · subst hff
        simp [footballFootball] at hrow
  · constructor
    · intro h
      have hσ : σ = balletFootball := sigma_eq_balletFootball σ hrow hcol
      subst hσ
      exact False.elim (balletFootball_not_pureNash h)
    · intro h
      rcases h with hbb | hff
      · subst hbb
        simp [balletBallet] at hcol
      · subst hff
        simp [footballFootball] at hrow
  · constructor
    · intro h
      have hσ : σ = footballBallet := sigma_eq_footballBallet σ hrow hcol
      subst hσ
      exact False.elim (footballBallet_not_pureNash h)
    · intro h
      rcases h with hbb | hff
      · subst hbb
        simp [balletBallet] at hrow
      · subst hff
        simp [footballFootball] at hcol
  · constructor
    · intro _
      right
      exact sigma_eq_footballFootball σ hrow hcol
    · intro h
      rcases h with hbb | hff
      · subst hbb
        simp [balletBallet] at hrow
      · subst hff
        exact footballFootball_is_pureNash

theorem balletBallet_is_equilibrium :
    BoS.IsEquilibrium BoS.unconstrainedFeasible balletBallet := by
  rw [BoS.isEquilibrium_unconstrained_iff_isPureNash]
  exact balletBallet_is_pureNash

theorem footballFootball_is_equilibrium :
    BoS.IsEquilibrium BoS.unconstrainedFeasible footballFootball := by
  rw [BoS.isEquilibrium_unconstrained_iff_isPureNash]
  exact footballFootball_is_pureNash
