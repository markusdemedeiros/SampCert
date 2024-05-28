/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.Util.Gaussian.DiscreteGaussian
import SampCert.Util.Gaussian.GaussBound
import SampCert.Util.Gaussian.GaussConvergence
import SampCert.Util.Gaussian.GaussPeriodicity
import SampCert.Util.Shift
import SampCert.DifferentialPrivacy.RenyiDivergence
import SampCert.Samplers.GaussianGen.Basic

/-!
# Concentrated Bound

This file proves

-/

open Real Nat

lemma sg_sum_pos' {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (α : ℝ)  :
  0 < ((gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x)^α := by
  apply rpow_pos_of_pos
  rw [div_pos_iff]
  left
  constructor
  . apply exp_pos
  . apply sum_gauss_term_pos h

lemma SG_Renyi_simplify {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) :
  (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' (x : ℤ), (gauss_term_ℝ σ μ) x) x ^ α *
      (fun (x : ℤ) => (gauss_term_ℝ σ ν) x / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x) x ^ (1 - α)
    = (gauss_term_ℝ σ μ) x ^ α * (gauss_term_ℝ σ ν) x ^ (1 - α) / ∑' (x : ℤ), (gauss_term_ℝ σ ν) x := by
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  simp
  conv =>
    left
    ring_nf
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  rw [shifted_gauss_sum_0 h]
  rw [shifted_gauss_sum_0 h]
  conv =>
    left
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
  conv =>
    left
    rw [mul_assoc]
    right
    right
    rw [X]
    rw [rpow_add D]
    rw [mul_comm]
    rw [mul_assoc]
    simp
    right
    rw [← rpow_add D]
    simp
  simp
  conv =>
    left
    rw [← mul_assoc]
  rfl

/--
Alternative definition for the Renyi Divergence.
MARKUSDE: Try to get rid of this, if we can.
-/
noncomputable def RenyiDivergence' (p q : T → ℝ) (α : ℝ) : ℝ :=
  (1 / (α - 1)) * Real.log (∑' x : T, (p x)^α  * (q x)^(1 - α))

/--
Upper bound on the Renyi Divergence between gaussians for any paramater `α > 1`.
-/
theorem RenyiDivergenceBound {σ : ℝ} (h : σ ≠ 0) (μ : ℤ) (α : ℝ) (h' : 1 < α) :
  RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x)
                  (fun (x : ℤ) => (gauss_term_ℝ σ (0 : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ (0 : ℤ)) x)
                  α ≤ α * (μ^2 / (2 * σ^2)) := by
  unfold RenyiDivergence'
  have A : 0 < 1 / (α - 1) := by
    simp [h']
  rw [← le_div_iff' A]
  refine Real.exp_le_exp.mp ?_
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have B' : ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ 0) x := by
    unfold gauss_term_ℝ
    intro x
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  have C' : 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_nonneg]
    apply le_of_lt
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  have D : 0 < (∑' (x : ℤ), (gauss_term_ℝ σ 0) x)⁻¹ := by
    rw [inv_pos]
    conv =>
      right
      rw [← Int.cast_zero]
    apply sum_gauss_term_pos h
  rw [exp_log]
  . conv =>
      left
      ring_nf
      right
      intro x
      rw [mul_rpow (B μ x) (C μ)]
      rw [mul_rpow (B' x) C']
    -- First, I work on the denominator
    rw [shifted_gauss_sum_0 h]
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      rw [← mul_assoc]
      left
      rw [mul_comm]
    have X : ∀ x y : ℝ, x - y = x + (-y) := fun x y => rfl
    conv =>
      left
      right
      intro x
      rw [mul_assoc]
      right
      right
      rw [X]
      rw [rpow_add D]
      rw [mul_comm]
      rw [mul_assoc]
      simp
      right
      rw [← rpow_add D]
      simp
    simp
    conv =>
      left
      right
      intro x
      rw [← mul_assoc]
    rw [tsum_mul_right]
    rw [← division_def]
    -- Now, I work on the numerator
    conv =>
      left
      left
      unfold gauss_term_ℝ
      right
      intro x
      rw [← Real.exp_mul]
      rw [← Real.exp_mul]
      rw [← exp_add]
      rw [← mul_div_right_comm]
      rw [← mul_div_right_comm]
      rw [div_add_div_same]
      rw [mul_sub_left_distrib]
      right
      left
      simp
      ring_nf
    have E : ∀ x : ℤ, x * μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = - (x - α * μ)^2 + α * (α -1) * μ^2 := by
      intro x
      ring_nf
    conv =>
      left
      left
      right
      intro x
      rw [E]
      rw [_root_.add_div]
      rw [exp_add]
    rw [tsum_mul_right]
    rw [mul_comm]
    rw [mul_div_assoc]
    have F := sum_gauss_term_bound h (α * μ)
    unfold gauss_term_ℝ
    unfold gauss_term_ℝ at F
    --clear A B B' C C' D X E
    have X : 0 < ∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)) := by
      conv =>
        right
        rw [← Int.cast_zero]
      apply sum_gauss_term_pos h
    have G := @div_le_one ℝ _ (∑' (x : ℤ), rexp (-(↑x - α * ↑μ) ^ 2 / (2 * σ^2))) (∑' (x : ℤ), rexp (-(↑x - 0) ^ 2 / (2 * σ^2)))
    replace G := (G X).2 F
    clear X F
    conv =>
      right
      rw [← mul_rotate]
      right
      left
      rw [mul_comm]
    conv =>
      right
      rw [← mul_div_assoc]
    apply mul_le_of_le_one_right _ G
    apply exp_nonneg
  . apply tsum_pos _ _ 0 _
    . simp -- some of this proof is similar to the one just above and needs to be hoisted
      conv =>
        right
        intro x
        rw [division_def]
        rw [division_def]
        rw [mul_rpow (B μ x) (C μ)]
        rw [mul_rpow (B' x) C']
      conv =>
        right
        intro x
        rw [mul_assoc]
        right
        rw [← mul_assoc]
        left
        rw [mul_comm]
      conv =>
        right
        intro x
        ring_nf
      apply Summable.mul_right
      apply Summable.mul_right
      unfold gauss_term_ℝ
      conv =>
        right
        intro x
        rw [← Real.exp_mul]
        rw [← Real.exp_mul]
        rw [← exp_add]
        rw [← mul_div_right_comm]
        rw [← mul_div_right_comm]
        rw [div_add_div_same]
        rw [mul_sub_left_distrib]
        rw [sub_zero]
        rw [mul_one]
        right
        left
        ring_nf
      have X : ∀ x : ℤ, x * ↑μ * α * 2 + (-x ^ 2 - μ ^ 2 * α) = -(x - α * μ)^2 + α * (α -1) * μ^2 := by
        intro x
        ring_nf
      conv =>
        right
        intro x
        rw [X]
        rw [← div_add_div_same]
        rw [exp_add]
      apply Summable.mul_right
      apply summable_gauss_term' h
    . intro i
      apply le_of_lt
      rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' h
      . apply sg_sum_pos' h
    . rw [mul_pos_iff]
      left
      constructor
      . apply sg_sum_pos' h
      . apply sg_sum_pos' h

-- MARKUSDE: Dead code
-- theorem SG_shift {σ : ℝ} (h : σ ≠ 0) (μ : ℝ) (τ : ℤ) :
--   (∑' x : ℤ, (gauss_term_ℝ σ μ) (x + τ)) = ∑' x : ℤ, (gauss_term_ℝ σ μ) x := by
--   have B := tsum_shift (fun x : ℤ => (gauss_term_ℝ σ μ) x) τ
--   rw [← B]
--   . apply tsum_congr
--     intro b
--     simp
--   . intro ν
--     conv =>
--       right
--       intro x
--       rw [SGShift]
--     apply summable_gauss_term' h

lemma  sg_mul_simplify (ss : ℝ) (x μ ν : ℤ) :
  rexp (-(x - μ) ^ 2 / (2 * ss)) ^ α * rexp (-(x - ν) ^ 2 / (2 * ss)) ^ (1 - α)
  = rexp (-((x - μ) ^ 2 * α + (x - ν) ^ 2 * (1 - α)) / (2 * ss)) := by
  rw [← Real.exp_mul]
  rw [← Real.exp_mul]
  rw [← exp_add]
  rw [← mul_div_right_comm]
  rw [← mul_div_right_comm]
  rw [div_add_div_same]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_mul_eq_neg_mul]
  rw [← neg_add]

lemma SG_Renyi_shift {σ : ℝ} (h : σ ≠ 0) (α : ℝ) (μ ν τ : ℤ) :
  RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ μ) x / ∑' x : ℤ, (gauss_term_ℝ σ μ) x) (fun (x : ℤ) => (gauss_term_ℝ σ ν) x / ∑' x : ℤ, (gauss_term_ℝ σ ν) x) α
    = RenyiDivergence' (fun (x : ℤ) => (gauss_term_ℝ σ ((μ + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x) (fun (x : ℤ) => (gauss_term_ℝ σ ((ν + τ) : ℤ)) x / ∑' x : ℤ, (gauss_term_ℝ σ ((ν + τ) : ℤ)) x) α := by
  unfold RenyiDivergence'
  congr 2
  conv =>
    left
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  conv =>
    right
    right
    intro x
    rw [SG_Renyi_simplify h]
    rw [division_def]
  rw [tsum_mul_right]
  rw [tsum_mul_right]
  rw [shifted_gauss_sum_0 h]
  rw [shifted_gauss_sum_0 h]
  congr 1

  -- re-indexing

  have A : ∀ μ : ℤ, ∀ x : ℤ, (gauss_term_ℝ σ ((μ + τ) : ℤ)) x =  (gauss_term_ℝ σ μ) (x - τ) := by
    intro x μ
    simp [gauss_term_ℝ]
    ring_nf
  conv =>
    right
    right
    intro x
    rw [A]
    rw [A]
  clear A

  -- Now for the crux of the proof

  unfold gauss_term_ℝ
  conv =>
    left
    right
    intro x
    rw [sg_mul_simplify]
  conv =>
    right
    right
    intro x
    rw [sub_sub]
    rw [sub_sub]
    rw [← Int.cast_add]
    rw [← Int.cast_add]
    rw [sg_mul_simplify]

  rw [← tsum_shift _ (-τ)]
  . apply tsum_congr
    intro b
    congr 6
    . simp
      ring_nf
    . simp
      ring_nf
  . intro β
    conv =>
      right
      intro x
      rw [Int.cast_add]
      rw [add_sub_assoc]
      rw [add_sub_assoc]
    have X : ∀ x : ℤ, ↑x * ↑β * 2 - ↑x * ↑μ * α * 2 + (↑x * α * ↑ν * 2 - ↑x * ↑ν * 2) + (↑x ^ 2 - ↑β * ↑μ * α * 2) +
                (↑β * α * ↑ν * 2 - ↑β * ↑ν * 2) +
              ↑β ^ 2 +
            (↑μ ^ 2 * α - α * ↑ν ^ 2) +
          ↑ν ^ 2 =
          (↑x ^ 2 - 2 * x * (-↑β + ↑μ * α - α * ↑ν + ↑ν)) + (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2) := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      right
      left
      right
      ring_nf
      rw [X]
    clear X
    have X : (- ↑β * ↑μ * α * 2 + ↑β * α * ↑ν * 2 - ↑β * ↑ν * 2 + ↑β ^ 2 + ↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)
      = (-↑β + ↑μ * α - α * ↑ν + ↑ν)^2 + (- ↑μ * α * ↑ν * 2 + ↑μ * α ^ 2 * ↑ν * 2 -
          ↑μ ^ 2 * α ^ 2 + α * ↑ν ^ 2 - α ^ 2 * ↑ν ^ 2 + α * ↑μ ^ 2) := by
      ring_nf
    conv =>
      right
      intro x
      rw [X]
      rw [← add_assoc]
    clear X
    have X : ∀ x : ℤ, (x - (-↑β + ↑μ * α - α * ↑ν + ↑ν))^2 = ↑x ^ 2 - 2 * ↑x * (-↑β + ↑μ * α - α * ↑ν + ↑ν) + (-↑β + ↑μ * α - α * ↑ν + ↑ν) ^ 2 := by
      intro x
      ring_nf
    conv =>
      right
      intro x
      rw [← X]
      rw [neg_add]
      rw [← div_add_div_same]
      rw [exp_add]
    clear X
    apply Summable.mul_right
    apply summable_gauss_term' h

/--
Upper bound on the Renyi Divergence between discrete gaussians for any paramater `α > 1`.
-/
theorem RenyiDivergenceBound_pre {σ α : ℝ} (h : σ ≠ 0) (h' : 1 < α) (μ ν : ℤ)   :
  RenyiDivergence' (fun (x : ℤ) => discrete_gaussian σ μ x)
                  (fun (x : ℤ) => discrete_gaussian σ ν x)
                  α ≤ α * (((μ - ν) : ℤ)^2 / (2 * σ^2)) := by
  unfold discrete_gaussian
  rw [SG_Renyi_shift h α μ ν (-ν)]
  rw [add_right_neg]
  apply  RenyiDivergenceBound h (μ + -ν) α h'

/--
Summand of Renyi divergence between discrete Gaussians is nonnegative.
-/
theorem RenyiSumSG_nonneg {σ α : ℝ} (h : σ ≠ 0) (μ ν n : ℤ) :
  0 ≤ discrete_gaussian σ μ n ^ α * discrete_gaussian σ ν n ^ (1 - α) := by
  have A := discrete_gaussian_nonneg h μ n
  have B := discrete_gaussian_nonneg h ν n
  rw [mul_nonneg_iff]
  left
  constructor
  . apply Real.rpow_nonneg A
  . apply Real.rpow_nonneg B

/--
Sum in Renyi divergence between discrete Gaussians is well-defined.
-/
theorem SummableRenyiGauss {σ : ℝ} (h : σ ≠ 0) (μ ν : ℤ) (α : ℝ) :
  Summable fun (x : ℤ) => discrete_gaussian σ μ x ^ α * discrete_gaussian σ ν x ^ (1 - α) := by
  simp [discrete_gaussian]
  have B : ∀ μ : ℤ, ∀ x : ℝ, 0 ≤ (gauss_term_ℝ σ μ) x := by
    intro μ x
    unfold gauss_term_ℝ
    apply exp_nonneg
  have C : ∀ μ : ℤ, 0 ≤ (∑' (x : ℤ), (gauss_term_ℝ σ μ) x)⁻¹ := by
    intro μ
    rw [inv_nonneg]
    apply le_of_lt
    apply sum_gauss_term_pos h
  conv =>
    right
    intro x
    rw [division_def]
    rw [division_def]
    rw [mul_rpow (B μ x) (C μ)]
    rw [mul_rpow (B ν x) (C ν)]
  conv =>
    right
    intro x
    rw [mul_assoc]
    right
    rw [← mul_assoc]
    left
    rw [mul_comm]
  conv =>
    right
    intro x
    ring_nf
  apply Summable.mul_right
  apply Summable.mul_right
  unfold gauss_term_ℝ
  conv =>
    right
    intro x
    rw [← Real.exp_mul]
    rw [← Real.exp_mul]
    rw [← exp_add]
    rw [← mul_div_right_comm]
    rw [← mul_div_right_comm]
    rw [div_add_div_same]
    rw [mul_sub_left_distrib]
    rw [mul_one]
    right
    left
    ring_nf

  have X : ∀ x : ℤ,
    ↑x * ↑μ * α * 2 - ↑x * α * ↑ν * 2 + ↑x * ↑ν * 2 + (-↑x ^ 2 - ↑μ ^ 2 * α) + (α * ↑ν ^ 2 - ↑ν ^ 2)
           = - ((↑x ^ 2 - 2 * x * (↑μ * α - α * ↑ν + ↑ν)) + (↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)) := by
        intro x
        ring_nf
  conv =>
    right
    intro x
    rw [X]
  clear X

  have X : (↑μ ^ 2 * α - α * ↑ν ^ 2 + ↑ν ^ 2)
    = (↑μ * α - α * ↑ν + ↑ν)^2 + (- ↑μ * α * ↑ν * 2 + ↑μ * α ^ 2 * ↑ν * 2 -
        ↑μ ^ 2 * α ^ 2 + α * ↑ν ^ 2 - α ^ 2 * ↑ν ^ 2 + α * ↑μ ^ 2) := by
    ring_nf
  conv =>
    right
    intro x
    rw [X]
    rw [← add_assoc]
  clear X

  have X : ∀ x : ℤ, (x - (↑μ * α - α * ↑ν + ↑ν))^2 = ↑x ^ 2 - 2 * ↑x * (↑μ * α - α * ↑ν + ↑ν) + (↑μ * α - α * ↑ν + ↑ν) ^ 2 := by
    intro x
    ring_nf
  conv =>
    right
    intro x
    rw [← X]
    rw [neg_add]
    rw [← div_add_div_same]
    rw [exp_add]
  clear X
  apply Summable.mul_right
  apply summable_gauss_term' h

/--
Upper bound on Renyi divergence between discrete Gaussians.
-/
theorem RenyiDivergenceBound' {σ α : ℝ} (h : σ ≠ 0) (h' : 1 < α) (μ ν : ℤ)   :
  RenyiDivergence (fun (x : ℤ) => ENNReal.ofReal (discrete_gaussian σ μ x))
                  (fun (x : ℤ) => ENNReal.ofReal (discrete_gaussian σ ν x))
                  α ≤ α * (((μ - ν) : ℤ)^2 / (2 * σ^2)) := by
  have A : RenyiDivergence (fun (x : ℤ) => ENNReal.ofReal (discrete_gaussian σ μ x))
                  (fun (x : ℤ) => ENNReal.ofReal (discrete_gaussian σ ν x))
                  α  = RenyiDivergence' (fun (x : ℤ) => discrete_gaussian σ μ x)
                  (fun (x : ℤ) => discrete_gaussian σ ν x)
                  α  := by
    unfold RenyiDivergence
    unfold RenyiDivergence'
    congr
    simp
    have A₁ : ∀ x : ℤ, 0 ≤ discrete_gaussian σ μ x ^ α := by
      intro x
      apply Real.rpow_nonneg
      apply discrete_gaussian_nonneg h μ x
    conv =>
      left
      right
      right
      intro x
      rw [ENNReal.ofReal_rpow_of_pos (discrete_gaussian_pos h μ x)]
      rw [ENNReal.ofReal_rpow_of_pos (discrete_gaussian_pos h ν x)]
      rw [← ENNReal.ofReal_mul (A₁ x)]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    . simp
      apply tsum_nonneg
      intro i
      apply RenyiSumSG_nonneg h
    . apply RenyiSumSG_nonneg h
    . apply SummableRenyiGauss h
  rw [A]
  apply RenyiDivergenceBound_pre h h'

namespace SLang

/--
Upper bound on Renyi divergence between outputs of the ``SLang`` discrete Gaussian sampler.
-/
theorem DiscreteGaussianGenSampleZeroConcentrated {α : ℝ} (h : 1 < α) (num : PNat) (den : PNat) (μ ν : ℤ) :
  RenyiDivergence ((DiscreteGaussianGenSample num den μ)) (DiscreteGaussianGenSample num den ν) α ≤
  α * (((μ - ν) : ℤ)^2 / (2 * ((num : ℝ) / (den : ℝ))^2)) := by
  have A : (num : ℝ) / (den : ℝ) ≠ 0 := by
    simp only [ne_eq, div_eq_zero_iff, cast_eq_zero, PNat.ne_zero, or_self, not_false_eq_true]
  conv =>
    left
    congr
    . intro x
      rw [DiscreteGaussianGenSample_apply]
    . intro x
      rw [DiscreteGaussianGenSample_apply]
    . skip
  apply RenyiDivergenceBound' A h

end SLang
