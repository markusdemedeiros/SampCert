/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.ParHistogram.Code
import SampCert.DifferentialPrivacy.Queries.Histogram.Properties
import SampCert.DifferentialPrivacy.Sensitivity
import SampCert.DifferentialPrivacy.Abstract

/-!
# ``privParHistogram`` Properties

This file proves abstract differential privacy for the parallel noised histogram.
-/

open Classical Nat Int Real

noncomputable section

namespace SLang

variable {T : Type}
variable [dps : DPPar T]
variable [dpn : DPNoise dps.toDPSystem]
variable [HT : Inhabited T]

variable (numBins : ℕ+)
variable (B : Bins T numBins)

variable (ε₁ ε₂ : ℕ+) (ε : NNReal) (HN_bin : dpn.noise_priv ε₁ ε₂ ε)

/--
DP bound for a noised bin count
-/
lemma privParNoisedBinCount_DP  (b : Fin numBins) :
  dps.prop (privParNoisedBinCount numBins B ε₁ ε₂ b) ε := by
  unfold privParNoisedBinCount
  apply dpn.noise_prop HN_bin
  apply exactBinCount_sensitivity


-- lemma privParNoisedHistogramAux_DP (n : ℕ) (Hn : n < numBins) :
--     dps.prop (privParNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (2 * ε) := by
--   induction n
--   · unfold privParNoisedHistogramAux
--     simp
--     apply dps.postprocess_prop
--     apply dps.prop_par
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--     -- apply dps.compose_prop
--     -- · -- unfold privNoisedBinCount
--     --   -- apply dpn.noise_prop HN_bin
--     --   -- apply exactBinCount_sensitivity
--     --   sorry
--     -- · apply dps.const_prop; rfl
--   · sorry

/-


/--
DP bound for intermediate steps in the histogram calculation.
-/
lemma privNoisedHistogramAux_DP (n : ℕ) (Hn : n < numBins) :
  dps.prop (privNoisedHistogramAux numBins B ε₁ ε₂ n Hn) (n.succ * (ε / numBins)) := by
  induction n
  · unfold privNoisedHistogramAux
    simp
    apply dps.postprocess_prop
    apply dps.compose_prop (AddLeftCancelMonoid.add_zero _)
    · apply privNoisedBinCount_DP; apply HN_bin
    · apply dps.const_prop; rfl
  · rename_i _ IH
    simp [privNoisedHistogramAux]
    apply dps.postprocess_prop
    apply dps.compose_prop ?arithmetic
    · apply privNoisedBinCount_DP; apply HN_bin
    · apply IH
    case arithmetic => simp; ring_nf

/--
DP bound for a noised histogram
-/
lemma privNoisedHistogram_DP :
  dps.prop (privNoisedHistogram numBins B ε₁ ε₂) ε := by
  unfold privNoisedHistogram
  apply (DPSystem_prop_ext _ ?HEq ?Hdp)
  case Hdp => apply privNoisedHistogramAux_DP; apply HN_bin
  case HEq => simp [predBins, mul_div_left_comm]

/--
DP bound for the thresholding maximum
-/
lemma privMaxBinAboveThreshold_DP (τ : ℤ) :
  dps.prop (privMaxBinAboveThreshold numBins B ε₁ ε₂ τ) ε := by
  unfold privMaxBinAboveThreshold
  apply dps.postprocess_prop
  apply privNoisedHistogram_DP
  apply HN_bin

end SLang
-/
