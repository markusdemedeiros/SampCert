/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.DP
import SampCert.DifferentialPrivacy.Pure.Mechanism.Basic
import SampCert.DifferentialPrivacy.Pure.AdaptiveComposition
import SampCert.DifferentialPrivacy.Pure.Postprocessing
import SampCert.DifferentialPrivacy.Pure.Const
import SampCert.DifferentialPrivacy.Pure.Par

/-!
# Pure DP system
-/

namespace SLang

variable { T : Type }

/--
Pure ε-DP with noise drawn from the discrete Laplace distribution.
-/
instance PureDPSystem : DPSystem T where
  prop := PureDP
  of_app_dp := pure_of_adp
  prop_adp := pure_ApproximateDP
  prop_mono := PureDP_mono
  adaptive_compose_prop := by
    intros; apply PureDP_ComposeAdaptive' <;> trivial
  postprocess_prop := by
    intros; apply PureDP_PostProcess; trivial
  const_prop := by
    intros; apply PureDP_privConst; trivial

instance laplace_pureDPSystem : DPNoise (@PureDPSystem T) where
  noise := privNoisedQueryPure
  noise_priv := laplace_pureDP_noise_priv
  noise_prop := by
    intros; apply privNoisedQueryPure_DP <;> trivial

instance PureDPParSystem : DPPar T where
  prop_par := pureDP_priv_Par

end SLang
