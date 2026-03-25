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

def stagHare : SH.Profile :=
  fun
  | row => stag
  | col => hare

def hareStag : SH.Profile :=
  fun
  | row => hare
  | col => stag

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

theorem stagHare_not_pureNash :
    ¬ SH.IsPureNash stagHare := by
  intro h
  have h₁ := h row hare
  simp [stagHare, SH, SHUtility,
    UtilityModel.deviate, EconModel.deviate] at h₁
  linarith

theorem hareStag_not_pureNash :
    ¬ SH.IsPureNash hareStag := by
  intro h
  have h₁ := h col hare
  simp [hareStag, SH, SHUtility,
    UtilityModel.deviate, EconModel.deviate] at h₁
  linarith

lemma sigma_eq_stagStag
    (σ : SH.Profile)
    (hrow : σ row = stag)
    (hcol : σ col = stag) :
    σ = stagStag := by
  funext i
  cases i <;> assumption

lemma sigma_eq_stagHare
    (σ : SH.Profile)
    (hrow : σ row = stag)
    (hcol : σ col = hare) :
    σ = stagHare := by
  funext i
  cases i <;> assumption

lemma sigma_eq_hareStag
    (σ : SH.Profile)
    (hrow : σ row = hare)
    (hcol : σ col = stag) :
    σ = hareStag := by
  funext i
  cases i <;> assumption

lemma sigma_eq_hareHare
    (σ : SH.Profile)
    (hrow : σ row = hare)
    (hcol : σ col = hare) :
    σ = hareHare := by
  funext i
  cases i <;> assumption

theorem isPureNash_iff
    (σ : SH.Profile) :
    SH.IsPureNash σ ↔ σ = stagStag ∨ σ = hareHare := by
  cases hrow : σ row <;> cases hcol : σ col
  · constructor
    · intro _
      left
      exact sigma_eq_stagStag σ hrow hcol
    · intro h
      rcases h with hss | hhh
      · subst hss
        exact stagStag_is_pureNash
      · subst hhh
        simp [hareHare] at hrow
  · constructor
    · intro h
      have hσ : σ = stagHare := sigma_eq_stagHare σ hrow hcol
      subst hσ
      exact False.elim (stagHare_not_pureNash h)
    · intro h
      rcases h with hss | hhh
      · subst hss
        simp [stagStag] at hcol
      · subst hhh
        simp [hareHare] at hrow
  · constructor
    · intro h
      have hσ : σ = hareStag := sigma_eq_hareStag σ hrow hcol
      subst hσ
      exact False.elim (hareStag_not_pureNash h)
    · intro h
      rcases h with hss | hhh
      · subst hss
        simp [stagStag] at hrow
      · subst hhh
        simp [hareHare] at hcol
  · constructor
    · intro _
      right
      exact sigma_eq_hareHare σ hrow hcol
    · intro h
      rcases h with hss | hhh
      · subst hss
        simp [stagStag] at hrow
      · subst hhh
        exact hareHare_is_pureNash

theorem stagStag_is_equilibrium :
    SH.IsEquilibrium SH.unconstrainedFeasible stagStag := by
  rw [SH.isEquilibrium_unconstrained_iff_isPureNash]
  exact stagStag_is_pureNash

theorem hareHare_is_equilibrium :
    SH.IsEquilibrium SH.unconstrainedFeasible hareHare := by
  rw [SH.isEquilibrium_unconstrained_iff_isPureNash]
  exact hareHare_is_pureNash
