/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Foundations.Basic
import SampCert.DifferentialPrivacy.Queries.Count.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedSum.Basic
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Code

/-!
# ``privNoisedBoundedMean`` Properties

This file proves abstract differential privacy for ``privNoisedBoundedMean``.
-/

open Classical Nat Int Real Rat

noncomputable section

namespace SLang

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

lemma budget_split (ε₁ ε₂ : ℕ+) :
  (ε₁ : NNReal) / (ε₂ : NNReal) = (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) + (ε₁ : NNReal) / ((2 * ε₂) : ℕ+) := by
  field_simp
  ring_nf

/--
DP bound for noised mean.
-/
theorem privNoisedBoundedMean_DP (U : ℕ+) (ε₁ ε₂ : ℕ+)
  (HP_half : dpn.noise_priv ε₁ (2 * ε₂) (ε₁ / ↑(2 * ε₂))) :
  dps.prop (privNoisedBoundedMean U ε₁ ε₂) ((ε₁ : NNReal) / ε₂) := by
  unfold privNoisedBoundedMean
  rw [bind_bind_indep]
  apply dps.postprocess_prop
  apply dps.compose_prop ?SC1
  · apply privNoisedBoundedSum_DP
    apply HP_half
  · apply privNoisedCount_DP
    apply HP_half

  case SC1 =>
    -- Arithmetic
    ring_nf
    rw [div_mul]
    congr
    simp

end SLang
