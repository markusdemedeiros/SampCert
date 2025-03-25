/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Code
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Properties

namespace SLang

variable (ε₁ ε₂ : ℕ+)

/--
Sum over a list, clipping each element to a maximum.

Similar to exactBoundedSum, however exactClippedSum allows m = 0.
-/
def exactClippedSum (m : ℕ) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n m)) l)

/--
Rate at which a given clipping thresold is impacting the accuracy of the sum.

Always negative or zero.
-/
def exactDiffSum (m : ℕ) (l : List ℕ) : ℤ := exactClippedSum m l - exactClippedSum (m + 1) l

/-
lemma exactDiffSum_nonpos : exactDiffSum point L ≤ 0 := by
  simp [exactDiffSum, exactClippedSum]
  induction L
  · simp
  · rename_i l ll IH
    simp
    apply le_trans
    · apply add_le_add
      · rfl
      · apply IH
    simp
-/

lemma exactDiffSum_singleton_le_1 : -1 ≤ exactDiffSum point [v] := by
  simp [exactDiffSum, exactClippedSum]
  cases (Classical.em (point ≤ v))
  · right
    trivial
  · left
    rename_i h
    simp at h
    rw [Int.min_def]
    simp
    split
    · linarith
    · linarith

lemma exactClippedSum_append : exactClippedSum i (A ++ B) = exactClippedSum i A + exactClippedSum i B := by
  simp [exactClippedSum]

lemma exactDiffSum_append : exactDiffSum i (A ++ B) = exactDiffSum i A + exactDiffSum i B := by
  simp [exactDiffSum]
  rw [exactClippedSum_append]
  rw [exactClippedSum_append]
  linarith

-- There is a value such that sampling at least that value implies the loop definitely terminiates
lemma lucky_guess : has_lucky exactDiffSum 0 := by
  intros τ l
  exists (List.length l + τ)
  intro A K' HK'
  apply ge_iff_le.mpr
  apply le_trans _ ?G1
  case G1 =>
    apply add_le_add
    · rfl
    · apply HK'
  conv =>
    lhs
    rw [<- zero_add τ]
  rw [<- add_assoc]
  simp
  clear HK'

  induction l
  · simp [exactDiffSum, exactClippedSum]
  · rename_i l0 ll IH
    simp
    rw [<- List.singleton_append]
    rw [exactDiffSum_append]
    rw [add_comm]
    repeat rw [<- add_assoc]
    rw [add_comm]
    repeat rw [<- add_assoc]
    rw [add_assoc]
    conv =>
      lhs
      rw [<- add_zero 0]
    apply add_le_add
    · apply IH
    · have H := @exactDiffSum_singleton_le_1 A l0
      linarith

def privUnboundedMax (ε₁ ε₂ : ℕ+) : List ℕ -> SPMF ℕ :=
  sv1_aboveThresh_PMF exactDiffSum 0 lucky_guess ε₁ ε₂

/-
/-
## Program version 0
  - Executable
  - Optimization of sv1: Tracks single state
  (Needs sv0 sv1 equivalence proof)
-/

def sv0_state : Type := ℕ × ℤ

def sv0_threshold (s : sv0_state) : ℕ := s.1

def sv0_noise (s : sv0_state) : ℤ := s.2

def sv0_aboveThreshC (τ : ℤ) (l : List ℕ) (s : sv0_state) : Bool :=
  decide (exactDiffSum (sv0_threshold s) l + (sv0_noise s) < τ)

def sv0_aboveThreshF (ε₁ ε₂ : ℕ+) (s : sv0_state) : SLang sv0_state := do
  let vn <- privNoiseGuess ε₁ ε₂
  let n := (sv0_threshold s) + 1
  return (n, vn)

def sv0_aboveThresh (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseThresh ε₁ ε₂
  let v0 <- privNoiseGuess ε₁ ε₂
  let sk <- probWhile (sv0_aboveThreshC τ l) (sv0_aboveThreshF ε₁ ε₂) (0, v0)
  return (sv0_threshold sk)
-/




-- Unused for now
lemma exactDiffSum_eventually_constant : ∃ K, ∀ K', K ≤ K' -> exactDiffSum K' l = 0 := by
  cases l
  · simp [exactDiffSum, exactClippedSum]
  · rename_i l0 ll
    let K := (@List.maximum_of_length_pos _ _ (l0 :: ll) (by simp))
    exists K
    intro K' HK'
    simp [exactDiffSum, exactClippedSum]
    rw [min_eq_left_iff.mpr ?G1]
    case G1 =>
      simp
      apply le_trans _ HK'
      apply List.le_maximum_of_length_pos_of_mem
      apply List.mem_cons_self
    rw [min_eq_left_iff.mpr ?G1]
    case G1 =>
      apply (@le_trans _ _ _ (↑K') _ _ (by simp))
      simp
      apply le_trans _ HK'
      apply List.le_maximum_of_length_pos_of_mem
      apply List.mem_cons_self
    conv =>
      enter [1, 1, 2, 1]
      rw [(@List.map_inj_left _ _ _ _ (fun n => ↑n)).mpr
            (by
              intro a Ha
              rw [min_eq_left_iff.mpr _]
              simp
              apply le_trans _ HK'
              apply List.le_maximum_of_length_pos_of_mem
              apply List.mem_cons_of_mem
              apply Ha)]
      rfl
    conv =>
      enter [1, 2, 2, 1]
      rw [(@List.map_inj_left _ _ _ _ (fun n => ↑n)).mpr
            (by
              intro a Ha
              rw [min_eq_left_iff.mpr _]
              apply (@le_trans _ _ _ (↑K') _ _ (by simp))
              simp
              apply le_trans _ HK'
              apply List.le_maximum_of_length_pos_of_mem
              apply List.mem_cons_of_mem
              apply Ha)]
      rfl
    simp


end SLang
