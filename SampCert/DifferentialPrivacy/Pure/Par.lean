/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import SampCert.DifferentialPrivacy.Generic
import SampCert.DifferentialPrivacy.Pure.DP

/-!
# Pure DP parallel composition

This file proves a DP bound for parallel composition
-/

noncomputable section

open Classical Nat Int Real ENNReal MeasureTheory Measure

namespace SLang

-- FIXME: Cleanup!
theorem privParCompose_DP_Bound {m1 : Mechanism T U} {m2 : Mechanism T V} {ε₁ ε₂ : NNReal} (f)
    (H1 : DP m1 ε₁) (H2 : DP m2 ε₂) : DP (privParCompose m1 m2 f) (max ε₁ ε₂) := by

  apply singleton_to_event
  apply event_to_singleton at H1
  apply event_to_singleton at H2

  -- Simplify the evaluation into a product
  rintro l₁ l₂ HN ⟨u, v⟩
  simp [DFunLike.coe]
  rw [privParCompose_eval, privParCompose_eval]
  rw [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv ?G1 ?G2]
  case G1 =>
    right
    apply PMF.apply_ne_top
  case G2 =>
    left
    apply PMF.apply_ne_top
  rw [mul_left_comm]
  repeat rw [<- mul_assoc]
  conv =>
    lhs
    enter [1, 1]
    rw [mul_comm]
    rw [<- ENNReal.div_eq_inv_mul]
  rw [mul_assoc]
  rw [<- ENNReal.div_eq_inv_mul]

  -- Now, use the neighbouring condition to turn one of the two terms into 1
  cases HN
  · rename_i l₁' l₂' t Hl₁ Hl₂
    simp only [Hl₁, Hl₂, List.filter_append, List.filter_singleton, Function.comp_apply]
    cases f t
    -- Addition
    · simp
      apply (le_trans ?G1)
      case G1 =>
        apply mul_le_mul
        · apply ENNReal.div_self_le_one
        · rfl
        · simp
        · simp
      simp
      transitivity
      · apply H2
        apply Neighbour.Addition
        · rfl
        · simp; rfl
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        apply le_trans (le_max_right ε₁.toReal ε₂.toReal)
        conv =>
          lhs
          rw [<- one_mul (max _ _)]
        simp
    · simp
      rw [mul_comm]
      apply (le_trans ?G1)
      case G1 =>
        apply mul_le_mul
        · apply ENNReal.div_self_le_one
        · rfl
        · simp
        · simp
      simp
      transitivity
      · apply H1
        apply Neighbour.Addition
        · rfl
        · simp; rfl
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
  · rename_i l₁' t l₂' Hl₁ Hl₂
    simp only [Hl₁, Hl₂, List.filter_append, List.filter_singleton, Function.comp_apply]
    cases f t
    · simp
      apply (le_trans ?G1)
      case G1 =>
        apply mul_le_mul
        · apply ENNReal.div_self_le_one
        · rfl
        · simp
        · simp
      simp
      transitivity
      · apply H2
        apply Neighbour.Deletion
        · simp
          rfl
        · rfl
      · apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
    · simp
      rw [mul_comm]
      apply (le_trans ?G1)
      case G1 =>
        apply mul_le_mul
        · apply ENNReal.div_self_le_one
        · rfl
        · simp
        · simp
      simp
      transitivity
      · apply H1
        apply Neighbour.Deletion
        · simp; rfl
        · rfl
      · apply ENNReal.ofReal_le_ofReal
        simp

theorem pureDP_priv_Par {m1 : Mechanism T U} {m2 : Mechanism T V} {ε₁ ε₂ ε: NNReal} :
    ε = max ε₁ ε₂ -> ∀f, DP m1 ε₁ -> DP m2 ε₂ -> DP (privParCompose m1 m2 f) ε :=
  (· ▸ privParCompose_DP_Bound)

end SLang
