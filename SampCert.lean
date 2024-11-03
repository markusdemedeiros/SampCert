/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.DifferentialPrivacy.Queries.BoundedMean.Basic
import SampCert.DifferentialPrivacy.Queries.Histogram.Basic
import SampCert.DifferentialPrivacy.ZeroConcentrated.System
import SampCert.DifferentialPrivacy.Pure.System
import SampCert.DifferentialPrivacy.Queries.HistogramMean.Properties
import SampCert.DifferentialPrivacy.Approximate.DP
import SampCert.Samplers.Gaussian.Properties
import Init.Data.UInt.Lemmas

open SLang PMF

def combineConcentrated := @privNoisedBoundedMean_DP zCDPSystem
def combinePure := @privNoisedBoundedMean_DP PureDPSystem

/-
##  Example: execute the histogram mean on a list
-/
section histogramMeanExample

def numBins : ℕ+ := 64

/-
Bin the infinite type ℕ with clipping
-/
def bin (n : ℕ) : Fin numBins :=
  { val := min (Nat.log 2 n) (PNat.natPred numBins),
    isLt := by
      apply min_lt_iff.mpr
      right
      exact Nat.lt_of_sub_eq_succ rfl
  }

/-
Return an upper bound on the bin value, clipped to 2^(1 + numBins)
-/
def unbin (n : Fin numBins) : ℕ+ := 2 ^ (1 + n.val)

noncomputable def combineMeanHistogram : Mechanism ℕ (Option ℚ) :=
  privMeanHistogram PureDPSystem laplace_pureDPSystem numBins { bin } unbin 1 20 2 1 20


-- (A) Can I even do this and run it?
-- (B) Can I automate this
def privNoisedCound_cmp (l : List ℕ) : SLang.has_cmp (@privNoisedCount _ PureDPSystem laplace_pureDPSystem 1 20 l) := by
  simp only [DFunLike.coe, PMF.instFunLike]
  simp only [privNoisedCount, DPNoise.noise, privNoisedQueryPure, DiscreteLaplaceGenSamplePMF]
  simp only [DiscreteLaplaceGenSample]
  -- Eta conversion, why does this come up?
  suffices has_cmp (DiscreteLaplaceSample (OfNat.ofNat 1 * OfNat.ofNat 20) (OfNat.ofNat 1) >>= fun s => Pure.pure (s + exactCount l))  by trivial
  simp
  apply SLang.has_cmp_bind
  · unfold DiscreteLaplaceSample
    simp only [Bind.bind]
    apply SLang.has_cmp_bind
    · unfold probUntil
      simp only [Bind.bind]
      apply SLang.has_cmp_bind
      · sorry
      · intro _
        apply has_cmp_loop
        intro _
        unfold DiscreteLaplaceSampleLoop
        simp only [Bind.bind]
        apply SLang.has_cmp_bind
        · unfold DiscreteLaplaceSampleLoopIn2
          simp only [Bind.bind]
          apply SLang.has_cmp_bind
          · apply has_cmp_loop
            intro _
            unfold DiscreteLaplaceSampleLoopIn2Aux
            simp only [Bind.bind]
            apply has_cmp_bind
            · unfold BernoulliExpNegSample
              simp only [Bind.bind]
              split
              · apply has_cmp_bind
                · unfold BernoulliExpNegSampleUnit
                  simp only [Bind.bind]
                  apply has_cmp_bind
                  · unfold BernoulliExpNegSampleUnitAux
                    simp only [Bind.bind]
                    apply has_cmp_bind
                    · apply has_cmp_loop
                      intro _
                      unfold BernoulliExpNegSampleUnitLoop
                      simp only [Bind.bind]
                      apply has_cmp_bind
                      · unfold BernoulliSample
                        simp only [Bind.bind]
                        apply has_cmp_bind
                        · sorry
                        · sorry
                      · sorry
                    · sorry
                  · sorry
                · sorry
              · sorry
            · intro _
              simp only [Pure.pure]
              apply has_cmp_pure
          · sorry
        · intro _
          apply has_cmp_bind
          · unfold BernoulliSample
            simp only [Bind.bind]
            apply has_cmp_bind
            · unfold UniformSample
              simp only [Bind.bind]
              apply has_cmp_bind
              · unfold probUntil
                simp only [Bind.bind]
                apply has_cmp_bind
                · sorry
                · intro _
                  apply has_cmp_loop
                  intro _
                  unfold UniformPowerOfTwoSample
                  unfold probUniformP2
                  sorry
              · intro _
                apply has_cmp_pure
            · intro _
              apply has_cmp_pure
          · intro _
            apply has_cmp_pure
    · intro _
      apply has_cmp_pure
  · intro _
    apply has_cmp_pure


end histogramMeanExample

-- The following is unsound and should NOT be part of the code
-- We are using it for now until the Python FFI is richer
@[extern "dirty_io_get"]
opaque DirtyIOGet(x : IO ℤ) : UInt32

lemma UInt32.toNa_of_non_zero {n : UInt32} (h : n ≠ 0) :
  0 < n.toNat := by
  have A : n.toNat ≠ 0 := by
    rw [← UInt32.zero_toNat]
    by_contra
    rename_i h'
    have B := UInt32.toNat.inj h'
    contradiction
  exact Nat.zero_lt_of_ne_zero A

@[export dgs_get]
def DiscreteGaussianSampleGet (num den : UInt32) (mix: UInt32) : UInt32 := Id.run do
  if h₁ : num = 0 then
    panic "DiscreteGaussianSampleGet was called with num = 0"
  else if h₂ : den = 0 then
    panic "DiscreteGaussianSampleGet was called with den = 0"
  else
    let z : IO ℤ ← run <| DiscreteGaussianPMF ⟨ num.toNat , UInt32.toNa_of_non_zero h₁ ⟩ ⟨ den.toNat , UInt32.toNa_of_non_zero h₂ ⟩ mix.toNat
    return DirtyIOGet z
