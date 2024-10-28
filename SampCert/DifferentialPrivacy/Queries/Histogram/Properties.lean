/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.Histogram.Code
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privHistogram`` Properties

This file proves abstract differential privacy for the noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPSystem T]
variable [dpn : DPNoise dps]
variable [HT : Inhabited T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

/-
exactBinCount is 1-sensitive
-/
theorem exactBinCount_sensitivity (b : Fin numBins) : sensitivity (exactBinCount numBins B b) 1 := by
  rw [sensitivity]
  intros l₁ l₂ HN
  cases HN
  · rename_i l₁' l₂' v' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v' l₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    aesop
  · rename_i l₁' v₁' l₂' v₂' Hl₁ Hl₂
    rw [ Hl₁, Hl₂ ]
    rw [exactBinCount, exactBinCount]
    simp [List.filter_cons]
    -- There has to be a better way
    cases (Classical.em (B.bin v₁' = b)) <;> cases (Classical.em (B.bin v₂' = b))
    all_goals (rename_i Hrw1 Hrw2)
    all_goals (simp [Hrw1, Hrw2])

/--
DP bound for a noised bin count
-/
lemma privNoisedBinCount_DP (ε₁ ε₂ : ℕ+) (ε : NNReal) (b : Fin numBins)
  (HN_bin : dpn.noise_priv ε₁ (ε₂ * numBins) (ε / numBins)) :
  dps.prop (privNoisedBinCount numBins B ε₁ ε₂ b) (ε / numBins) := by
  unfold privNoisedBinCount
  apply dpn.noise_prop HN_bin
  apply exactBinCount_sensitivity

/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (ε₁ ε₂ : ℕ+) (ε : NNReal) (n : ℕ) (Hn : n < numBins)
  (HN_bin : dpn.noise_priv ε₁ (ε₂ * numBins) (ε / numBins)) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n.succ * (ε / numBins)) := by
  induction n
  · unfold privNoisedHistogramAux
    simp only [Nat.cast_zero, succ_eq_add_one, zero_add, Nat.cast_one, Nat.cast_mul, one_mul]
    apply DPSystem.postprocess_prop
    apply DPSystem.compose_prop ?SC1
    · apply privNoisedBinCount_DP
      apply HN_bin
    · apply DPSystem.const_prop
      rfl
    case SC1 => simp only [add_zero]
  · rename_i n IH
    unfold privNoisedHistogramAux
    simp only []
    apply DPSystem.postprocess_prop
    apply DPSystem.compose_prop ?SC1
    · apply privNoisedBinCount_DP
      apply HN_bin
    · apply IH
    case SC1 =>
      simp
      ring_nf

/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP (ε₁ ε₂ : ℕ+) (ε : NNReal) (HN_bin : dpn.noise_priv ε₁ (ε₂ * numBins) (ε / numBins)) :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) ε := by
  unfold privNoisedHistogram
  apply (DPSystem_prop_ext _ ?HEq ?Hdp)
  case Hdp =>
    apply privNoisedHistogramAux_DP
    apply HN_bin
  case HEq =>
    simp [predBins]
    simp [mul_div_left_comm]

/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (ε₁ ε₂ : ℕ+) (ε : NNReal) (τ : ℤ) (HN_bin : dpn.noise_priv ε₁ (ε₂ * numBins) (ε / numBins)) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) ε := by
  unfold privMaxBinAboveThreshold
  apply dps.postprocess_prop
  apply privNoisedHistogram_DP
  apply HN_bin

end SLang
