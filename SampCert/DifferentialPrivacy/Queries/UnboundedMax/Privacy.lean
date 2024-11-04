/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Properties
import SampCert.DifferentialPrivacy.Pure.System

noncomputable section

open Classical

namespace SLang

variable (ε₁ ε₂ : ℕ+)

-- FIXME: Move
lemma tsum_shift (Δ : ℤ) (f : ℤ → ENNReal) : (∑'(x : ℤ), f x = ∑'(x : ℤ), f (x + Δ)) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i => exact (fun x => x.1 + Δ)
  · simp [Function.Injective]
  · simp
    intro x Hx
    exists (x - Δ)
    simp
    trivial
  · intro
    rfl


lemma laplace_inequality' (τ τ' : ℤ) (Δ : ℕ+) :
      ((ENNReal.ofReal (Real.exp (-abs τ' / (Δ * ε₂ / ε₁)))) * ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 τ))) ≤
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) (τ + τ') := by
  simp [DiscreteLaplaceGenSamplePMF, PMF.instFunLike]
  generalize HA : (Real.exp (↑↑ε₁ / (↑↑Δ * ↑↑ε₂)) - 1) = A
  generalize HB : (Real.exp (↑↑ε₁ / (↑↑Δ * ↑↑ε₂)) + 1) = B
  generalize HC : ((Δ : Real) * ε₂ / ε₁) = C
  rw [<- ENNReal.ofReal_mul ?G1]
  case G1 => apply Real.exp_nonneg
  apply ENNReal.ofReal_le_ofReal
  conv =>
    lhs
    rw [mul_comm]
    repeat rw [mul_assoc]
  apply mul_le_mul_of_nonneg
  · rfl
  · rw [← Real.exp_add]
    apply Real.exp_monotone
    repeat rw [<- neg_div]
    rw [div_add_div_same]
    apply div_le_div_of_nonneg_right
    · simp
      have H := @abs_add_le ℝ _ _ _ τ τ'
      linarith
    · rw [<- HC]
      simp [div_nonneg_iff]
  · rw [<- HA]
    rw [<- HB]
    simp [div_nonneg_iff]
    left
    conv =>
      lhs
      rw [<- add_zero 0]
    apply add_le_add
    · apply Real.exp_nonneg
    · simp
  · apply Real.exp_nonneg

lemma laplace_inequality (τ τ' : ℤ) (Δ : ℕ+) :
      ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 τ)) ≤
      ((ENNReal.ofReal (Real.exp (abs τ' / (Δ * ε₂ / ε₁)))) *
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) (τ + τ')) := by
    apply le_trans _ ?G1
    case G1 =>
      apply ENNReal.mul_left_mono
      apply laplace_inequality'
    simp only []
    repeat rw [<- mul_assoc]
    conv =>
      lhs
      rw [<- one_mul (DiscreteLaplaceGenSamplePMF _ _ _  _)]
    apply mul_le_mul
    · apply Eq.le
      rw [<- ENNReal.ofReal_mul ?G1]
      case G1 => apply Real.exp_nonneg
      rw [<- Real.exp_add]
      symm
      simp
      rw [div_add_div_same]
      rw [div_eq_zero_iff]
      left
      simp
    · rfl
    · apply zero_le
    · apply zero_le



lemma sv8_privMax_pmf_DP (ε : NNReal) (Hε : ε = ε₁ / ε₂) : PureDPSystem.prop (@sv9_privMax_pmf PureDPSystem ε₁ ε₂) ε := by
  -- Unfold DP definitions
  simp [DPSystem.prop]
  apply singleton_to_event
  unfold DP_singleton
  intro l₁ l₂ Hneighbour point

  apply ENNReal.div_le_of_le_mul
  simp [sv9_privMax_pmf, DFunLike.coe, PMF.instFunLike]

  cases point
  · -- point = 0
    simp only [sv9_privMax]

    sorry


  · rename_i point
    -- point > 0
    -- proceed with the proof in the paper
    simp [sv9_privMax]

    -- Cancel out the deterministic parts
    conv =>
      enter [2]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i]
      rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_mul_left]
      enter [1, i_1]
      repeat rw [<- mul_assoc]
      enter [1]
      rw [mul_comm (ENNReal.ofReal _)]
      repeat rw [mul_assoc]
      rw [mul_comm (ENNReal.ofReal _)]
    conv =>
      enter [2, 1, i, 1, i_1]
      repeat rw [mul_assoc]
    conv =>
      enter [1, 1, i]
      rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro v0
    apply ENNReal.tsum_le_tsum
    intro vs
    apply ENNReal.mul_left_mono
    apply ENNReal.mul_left_mono

    -- Rearrange to put sums on the outside
    conv =>
      lhs
      enter [1, τ]
      rw [← ENNReal.tsum_mul_left]
      enter [1, vk]
    conv =>
      rhs
      rw [← ENNReal.tsum_mul_left]
      enter [1, τ]
      rw [← ENNReal.tsum_mul_left]
      rw [← ENNReal.tsum_mul_left]
      enter [1, vk]

    simp [sv8_cond, sv8_sum]

    -- Perform the changes of variables, so that the sums are pointwise le
    let cov_τ : ℤ := (sv8_G l₁ [] v0 vs) - (sv8_G l₂ [] v0 vs)
    let cov_vk : ℤ := exactDiffSum (point + 1) l₂ - exactDiffSum (point + 1) l₁ + cov_τ

    conv =>
      lhs
      rw [tsum_shift cov_τ]
      enter [1, τ]
      rw [tsum_shift cov_vk]
      enter [1, vk]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply ENNReal.tsum_le_tsum
    intro vk

    -- The change of variables make the conditional equal
    repeat rw [<- mul_assoc]
    apply mul_le_mul' _ ?G2
    case G2 =>
      apply Eq.le
      suffices ((sv8_G l₁ [] v0 ↑vs < τ + cov_τ) = (sv8_G l₂ [] v0 ↑vs < τ)) ∧
               ((τ + cov_τ ≤ exactDiffSum (point + 1) l₁ + (vk + cov_vk)) = (τ ≤ exactDiffSum (point + 1) l₂ + vk)) by simp_all
      apply And.intro
      · -- cov_τ
        apply propext
        dsimp [cov_τ]
        apply Iff.intro <;> intro _ <;> linarith
      · -- cov_vk
        apply propext
        dsimp [cov_vk]
        apply Iff.intro <;> intro _ <;> linarith

    -- Might be more sensitive
    let sens_cov_τ : ℤ := 1
    have Hsens_cov_τ : cov_τ ≤ sens_cov_τ := by
      dsimp [cov_τ]
      cases vs
      rename_i vs Hvs
      simp

      cases Hneighbour
      · rename_i A B C H1 H2
        simp [H1, H2]; clear H1 H2
        induction A
        · simp
          unfold sv8_G
          sorry
        · sorry
      · sorry
      · sorry

    -- Might be more sensitive in reality
    let sens_cov_vk : ℤ := 2
    have Hsens_cov_vk : cov_vk ≤ sens_cov_vk := by
      sorry

    simp [privNoiseThresh, privNoiseGuess,
         privNoiseZero, DPSystem.noise, privNoisedQueryPure]





    sorry
