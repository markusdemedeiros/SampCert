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

namespace SLang

variable { T : Type }

/--
Instance of a DP system for zCDP
-/
instance zCDPSystem : DPSystem T where
  prop := zCDP
  of_adp := sorry
  prop_adp := sorry -- zCDP_ApproximateDP
  prop_mono := sorry -- zCDP_mono
  -- noise := privNoisedQuery
  -- noise_prop := sorry -- privNoisedQuery_zCDP
  adaptive_compose_prop := sorry -- privComposeAdaptive_zCDP
  postprocess_prop := sorry -- privPostProcess_zCDP
  const_prop := sorry -- privConst_zCDP

/--
Gaussian noise for zCDP system
-/
instance gaussian_zCDPSystem : DPNoise zCDPsystem where
  noise := privNoisedQuery
  noise_priv := sorry
  noise_prop := sorry -- privNoisedQuery_zCDP

/--
Laplace noise for zCDP system
-/
instance laplace_zCDPSystem : DPNoise zCDPsystem where
  noise := sorry
  noise_priv := sorry
  noise_prop := sorry -- privNoisedQuery_zCDP


end SLang
