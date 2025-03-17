/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.ZeroConcentrated.DP
import SampCert.DifferentialPrivacy.ZeroConcentrated.Mechanism.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.AdaptiveComposition
import SampCert.DifferentialPrivacy.ZeroConcentrated.Postprocessing
import SampCert.DifferentialPrivacy.ZeroConcentrated.Const

/-!
# zCDP System

This file contains an instance of an abstract DP system associated to the discrete gaussian mechanisms.
-/

noncomputable section

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP
-/
instance zCDPSystem : DPSystem T where
  prop := zCDP
  of_app_dp := zCDP_of_adp
  prop_adp := by
    intros; apply zCDP_ApproximateDP <;> assumption
  prop_mono := by
    intro _ _ _ _ H HZ
    apply zCDP_mono H HZ
  adaptive_compose_prop := by
    intros _ _ _ _ _ _ _ _ _ HZ HZ2 Hε
    rw [<- Hε]
    apply privComposeAdaptive_zCDP
    apply HZ
    apply HZ2
  postprocess_prop := by
    intros _ _ _ _ _ _ HZ
    apply privPostProcess_zCDP
    apply HZ
  const_prop := by
    intros _ _ _ _ Hε
    rw [Hε]
    apply privConst_zCDP

def gaussian_zCDP_noise_priv (ε₁ ε₂ : ℕ+) (ε : NNReal) : Prop := (1/2) * ((ε₁ : NNReal) / ε₂)^2 ≤ ε

/--
Gaussian noise for zCDP system
-/
instance gaussian_zCDPSystem (T : Type) : DPNoise (@zCDPSystem T) where
  noise := privNoisedQuery
  noise_priv := gaussian_zCDP_noise_priv
  noise_prop := by
    intros _ _ _ _ _ H HS
    apply DPSystem.prop_mono ?G1
    · simp [DPSystem.prop]
      apply privNoisedQuery_zCDP
      apply HS
    · apply H

end SLang
