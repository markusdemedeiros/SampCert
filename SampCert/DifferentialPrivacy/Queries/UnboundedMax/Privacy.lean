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


lemma laplace_inequality_sub (τ τ' : ℤ) (Δ : ℕ+) :
      ((DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0 (τ + τ'))) ≤
      ((ENNReal.ofReal (Real.exp (abs τ' / (Δ * ε₂ / ε₁)))) *
      (DiscreteLaplaceGenSamplePMF (Δ * ε₂) ε₁ 0) τ) := by
    apply le_trans
    · apply laplace_inequality ε₁ ε₂ (τ + τ') (-τ') Δ
    apply Eq.le
    simp



lemma exactClippedSum_append : exactClippedSum i (A ++ B) = exactClippedSum i A + exactClippedSum i B := by
  simp [exactClippedSum]

lemma exactDiffSum_append : exactDiffSum i (A ++ B) = exactDiffSum i A + exactDiffSum i B := by
  simp [exactDiffSum]
  rw [exactClippedSum_append]
  rw [exactClippedSum_append]
  linarith

lemma sv8_sum_append : sv8_sum (A ++ B) [] v0 = sv8_sum A [] v0 + sv8_sum B [] v0 - v0 := by
  simp [sv8_sum]
  simp [exactDiffSum_append]
  linarith

lemma sv8_sum_comm : sv8_sum (A ++ B) vp v0 = sv8_sum (B ++ A) vp v0 := by
  unfold sv8_sum
  simp
  simp [exactDiffSum, exactClippedSum]
  linarith

lemma sv8_G_comm : sv8_G (A ++ B) vp v0 vf = sv8_G (B ++ A) vp v0 vf := by
  revert vp v0
  induction vf
  · intros
    apply sv8_sum_comm
  · intro v0 vp
    rename_i next rest IH
    unfold sv8_G
    rw [sv8_sum_comm]
    congr 1
    apply IH

-- -- IDK
-- lemma sv8_G_cons : sv8_G (x :: L) vp v0 vf = 0 := by
--   revert vp v0
--   induction vf
--   · intros v0 vp
--     simp [sv8_G]
--     s orry
--   · intro vp v0
--     simp [sv8_G]
--     s orry
--     -- unfold sv8_G

lemma exactDiffSum_nonpos : exactDiffSum point L ≤ 0 := by
  simp [exactDiffSum, exactClippedSum]
  induction L
  · simp
  · rename_i l ll IH
    simp
    apply le_trans
    · apply add_le_add
      · rfl
      · apply IH
    simp

lemma exactDiffSum_singleton_le_1 : -1 ≤ exactDiffSum point [v] := by
  simp [exactDiffSum, exactClippedSum]
  cases (Classical.em (point ≤ v))
  · right
    trivial
  · left
    rename_i h
    simp at h
    rw [Int.min_def]
    simp
    split
    · linarith
    · linarith


-- Coercions nonsense
lemma DS0 (H : Neighbour L1 L2) : ((exactDiffSum 0 L1) : ℝ) - (exactDiffSum 0 L2) ≤ 1 := by
  cases H
  · rename_i A B C H1 H2
    rw [H1, H2]
    repeat rw [exactDiffSum_append]
    simp
    apply neg_le.mp
    have _ := @exactDiffSum_singleton_le_1 0 C
    sorry

  · rename_i A B C H1 H2
    rw [H1, H2]
    repeat rw [exactDiffSum_append]
    simp
    have _ := @exactDiffSum_nonpos 0 C
    sorry

  · rename_i A B C D H1 H2
    rw [H1, H2]
    repeat rw [exactDiffSum_append]
    simp only [Int.cast_add, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub]
    sorry


lemma sv8_privMax_pmf_DP (ε : NNReal) (Hε : ε = ε₁ / ε₂) :
    PureDPSystem.prop (@sv9_privMax_pmf PureDPSystem laplace_pureDPSystem ε₁ ε₂) ε := by
  -- Unfold DP definitions
  simp [DPSystem.prop]
  apply singleton_to_event
  unfold DP_singleton
  intro l₁ l₂ Hneighbour point

  apply ENNReal.div_le_of_le_mul
  simp [sv9_privMax_pmf, DFunLike.coe, PMF.instFunLike]

  cases point
  · -- point = 0
    simp [sv9_privMax]

    -- Put sums on outside
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

    -- Change of variables
    let cov_τ : ℤ := 0
    let cov_vk : ℤ := exactDiffSum 0 l₂ - exactDiffSum 0 l₁ + cov_τ
    conv =>
      lhs
      rw [tsum_shift cov_τ]
      enter [1, τ]
      rw [tsum_shift cov_vk]
      enter [1, vk]
    conv =>
      rhs
      enter [1, τ, 1, vk]
    apply ENNReal.tsum_le_tsum
    intro τ
    apply ENNReal.tsum_le_tsum
    intro vk

    rw [<- mul_assoc]
    rw [<- mul_assoc]
    rw [<- mul_assoc]
    apply mul_le_mul
    · -- Laplace bound
      simp [cov_τ]
      rw [mul_assoc]
      apply ENNReal.mul_left_mono
      simp [privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure]
      apply le_trans
      · apply laplace_inequality_sub
      rw  [mul_comm]
      apply ENNReal.mul_left_mono
      rw [Hε]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_monotone
      simp [sens_cov_vk, sens_cov_τ]

      have X : |((exactDiffSum 0 l₂) : ℝ) - (exactDiffSum 0 l₁)| ≤ 1 := by
        -- simp [exactDiffSum, exactClippedSum, List.map_const']
        rw [abs_le]
        apply And.intro
        · apply neg_le.mp
          simp only [neg_sub]
          apply DS0
          apply Hneighbour
        · apply DS0
          apply Neighbour_symm
          apply Hneighbour

      ring_nf
      rw [InvolutiveInv.inv_inv]
      conv =>
        lhs
        rw [mul_comm]
        rw [<- mul_assoc]
        rw [<- mul_assoc]
        rw [mul_comm]
        enter [2]
        rw [mul_comm]
      simp
      apply le_trans _ X
      conv =>
        rhs
        rw [<- one_mul (abs _)]
      apply mul_le_mul
      · apply inv_le_one
        simp
      · rfl
      · apply abs_nonneg
      · simp




    · -- Conditionals should be equal
      suffices (τ + cov_τ ≤ sv8_sum l₁ [] (vk + cov_vk)) = (τ ≤ sv8_sum l₂ [] vk) by
        split <;> simp_all
      apply propext
      simp [sv8_sum, cov_vk]
      apply Iff.intro
      · intro _ ; linarith
      · intro _ ; linarith

    · apply zero_le
    · apply zero_le


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

    -- Prove sensitivity bound
    have Hsens_cov_τ : cov_τ ≤ sens_cov_τ := by
      dsimp [cov_τ]
      cases vs
      rename_i vs Hvs
      simp only []
      cases Hneighbour
      · rename_i A B n H1 H2
        rw [H1, H2]; clear H1 H2
        conv =>
          enter [1, 2, 1]
          rw [List.append_assoc]
        rw [@sv8_G_comm A ([n] ++ B)]
        sorry

      · rename_i A n B H1 H2
        rw [H1, H2]; clear H1 H2
        conv =>
          enter [1, 1, 1]
          rw [List.append_assoc]
        rw [@sv8_G_comm A ([n] ++ B)]
        sorry

      · rename_i A n1 B n2 H1 H2
        rw [H1, H2]; clear H1 H2
        conv =>
          enter [1, 1, 1]
          rw [List.append_assoc]
        conv =>
          enter [1, 2, 1]
          rw [List.append_assoc]
        rw [@sv8_G_comm A ([n1] ++ B)]
        rw [@sv8_G_comm A ([n2] ++ B)]
        sorry

    -- Prove sensitivity bound
    have Hsens_cov_vk : cov_vk ≤ sens_cov_vk := by
      dsimp [cov_vk]
      cases vs
      rename_i vs Hvs
      cases Hneighbour
      · rename_i _ _ n H1 H2
        rw [H1, H2]; clear H1 H2
        repeat rw [exactDiffSum_append]
        simp_all [sens_cov_vk, sens_cov_τ]
        have _ := @exactDiffSum_singleton_le_1 (point + 1) n
        have _ := @exactDiffSum_nonpos (point + 1) [n]
        linarith

      · rename_i _ n _ H1 H2
        rw [H1, H2]; clear H1 H2
        repeat rw [exactDiffSum_append]
        simp_all [sens_cov_vk, sens_cov_τ]
        have _ := @exactDiffSum_singleton_le_1 (point + 1) n
        have _ := @exactDiffSum_nonpos (point + 1) [n]
        linarith

      · rename_i n1 _ n2 H1 H2
        rw [H1, H2]; clear H1 H2
        repeat rw [exactDiffSum_append]
        simp_all [sens_cov_vk, sens_cov_τ]
        have _ := @exactDiffSum_singleton_le_1 (point + 1) n1
        have _ := @exactDiffSum_nonpos (point + 1) [n1]
        have _ := @exactDiffSum_singleton_le_1 (point + 1) n2
        have _ := @exactDiffSum_nonpos (point + 1) [n2]
        linarith

    simp [privNoiseThresh, privNoiseGuess, privNoiseZero, DPNoise.noise, privNoisedQueryPure]

    -- Apply the Laplace inequalities
    apply le_trans
    · apply mul_le_mul
      · apply laplace_inequality_sub
      · apply laplace_inequality_sub
      · apply zero_le
      · apply zero_le

    -- Cancel the Laplace samples
    conv =>
      lhs
      rw [mul_assoc]
      rw [mul_comm]
    conv =>
      rhs
      rw [mul_assoc]
      rw [mul_comm]
    repeat rw [mul_assoc]
    apply ENNReal.mul_left_mono
    conv =>
      lhs
      rw [mul_comm]
    repeat rw [mul_assoc]
    apply ENNReal.mul_left_mono

    -- Apply the ineuqalities
    rw [<- ENNReal.ofReal_mul ?G1]
    case G1 => apply Real.exp_nonneg
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_monotone
    apply @le_trans _ _ _ ((|sens_cov_τ| : ℝ) / (↑↑(2 * sens_cov_τ) * ↑↑ε₂ / ↑↑ε₁) + (|sens_cov_vk| : ℝ) / (↑↑(2 * sens_cov_vk) * ↑↑ε₂ / ↑↑ε₁))
    · apply add_le_add
      · simp
        apply div_le_div_of_nonneg_right
        · -- apply abs_le'.mpr
          sorry
        · apply mul_nonneg <;> simp
      · sorry
    simp [sens_cov_τ, sens_cov_vk]
    ring_nf
    rw [InvolutiveInv.inv_inv]
    rw [Hε]
    conv =>
      lhs
      enter [2, 1]
      rw [mul_comm]
    rw [<- add_mul]
    rw [<- add_mul]
    conv =>
      lhs
      enter [1, 1]
      rw [<- (one_mul (ε₁.val.cast))]
    rw [<- add_mul]
    repeat rw [div_eq_mul_inv]
    simp
    rw [one_add_one_eq_two]
    ring_nf
    rfl
