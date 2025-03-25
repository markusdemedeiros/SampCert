/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.AboveThresh.Code

namespace SLang

variable (T : ℤ) (ε₁ ε₂ : ℕ+)

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

-- "Sparse" algorithm as described in the proof of 3.25 of
-- Cynthia Dwork and Aaron Roth "The Algorithmic Foundations of Differential Privacy" (2014)

def shift_qs (n : ℕ) (qs : sv_query) : sv_query := fun i => qs (i + n)




def privSparse (qs : sv_query) (c : ℕ) : Mechanism ℕ (List ℕ) :=
  match c with
  | 0 => privConst []
  | Nat.succ c' =>
      privPostProcess
        (privComposeAdaptive
          (sorry : Mechanism ℕ ℕ)
          (fun n => privSparse (shift_qs n qs) c'))
      (fun (x, L) => x :: L)



-- def privParNoisedBinCount (ε₁ ε₂ : ℕ+) (b : Fin numBins) : Mechanism T ℤ :=
--   (dpn.noise (exactBinCount numBins B b) 1 ε₁ ε₂)
--
-- def privParNoisedHistogramAux (ε₁ ε₂ : ℕ+) (n : ℕ) (Hn : n < numBins) : Mechanism T (Histogram T numBins B) :=
--   let privParNoisedHistogramAux_rec :=
--     match n with
--     | Nat.zero => privConst (emptyHistogram numBins B)
--     | Nat.succ n' => privParNoisedHistogramAux ε₁ ε₂ n' (Nat.lt_of_succ_lt Hn)
--   privPostProcess
--     (privParCompose
--       (privParNoisedBinCount numBins B ε₁ ε₂ n)
--       privParNoisedHistogramAux_rec
--       (B.bin · = n))
--     (fun z => setCount numBins B z.2 n z.1)
--
-- /--
-- Histogram with noise added to each count
-- -/
-- def privParNoisedHistogram (ε₁ ε₂ : ℕ+) : Mechanism T (Histogram T numBins B) :=
--   privParNoisedHistogramAux numBins B ε₁ ε₂ (predBins numBins) (predBins_lt_numBins numBins)


def sv1_sparse (qs : sv_query) (T : ℤ) (ε₁ ε₂ : ℕ+) (c : ℕ) : SPMF (List ℕ) :=
  match c with
  | 0 => return []
  | Nat.succ c' => sorry
    -- privComposeAdaptive
    --   sorry -- (sv1_aboveThresh qs T ε₁ ε₂ l)
    --   sorry

end SLang
