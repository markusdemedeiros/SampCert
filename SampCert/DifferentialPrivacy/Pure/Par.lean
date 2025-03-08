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

set_option pp.coercions false

-- FIXME: Cleanup!
theorem privParComp_DP_Bound {m1 : Mechanism T U} {m2 : Mechanism T V} {ε₁ ε₂ : NNReal} (f)
    (H1 : DP m1 ε₁) (H2 : DP m2 ε₂) : DP (privParComp m1 m2 f) (2 * max ε₁ ε₂) := by

  apply singleton_to_event
  apply event_to_singleton at H1
  apply event_to_singleton at H2

  -- Simplify the evaluation into a product
  rintro l₁ l₂ HN ⟨u, v⟩
  simp [DFunLike.coe]
  rw [privParComp_eval, privParComp_eval]
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
        apply mul_le_mul
        · simp
        · rfl
        · apply le_max_of_le_right
          exact NNReal.zero_le_coe
        · simp
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
        conv =>
          lhs
          rw [<- one_mul (ε₁.toReal)]
        apply mul_le_mul
        · simp
        · apply le_max_left
        · apply NNReal.zero_le_coe
        · simp
  -- Deletion
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
        conv =>
          lhs
          rw [<- one_mul (ε₂.toReal)]
        apply mul_le_mul
        · simp
        · apply le_max_right
        · apply NNReal.zero_le_coe
        · simp
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
        apply Real.exp_monotone
        conv =>
          lhs
          rw [<- one_mul (ε₁.toReal)]
        apply mul_le_mul
        · simp
        · apply le_max_left
        · apply NNReal.zero_le_coe
        · simp
  -- Modification
  · rename_i l₁' t₁ l₂' t₂ Hl₁ Hl₂
    simp only [Hl₁, Hl₂, List.filter_append, List.filter_singleton, Function.comp_apply]
    have Hlem1 : ENNReal.ofReal (rexp ε₁.toReal) ≤ ENNReal.ofReal (rexp (2 * max ε₁.toReal ε₂.toReal)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_monotone
      conv =>
        lhs
        rw [<- one_mul (ε₁.toReal)]
      apply mul_le_mul
      · simp
      · apply le_max_left
      · apply NNReal.zero_le_coe
      · simp
    have Hlem2 : ENNReal.ofReal (rexp ε₂.toReal) ≤ ENNReal.ofReal (rexp (2 * max ε₁.toReal ε₂.toReal)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_monotone
      conv =>
        lhs
        rw [<- one_mul (ε₂.toReal)]
      apply mul_le_mul
      · simp
      · apply le_max_right
      · apply NNReal.zero_le_coe
      · simp
    cases f t₁ <;> cases f t₂ <;> simp [Function.comp]
    · conv=>
        rhs
        rw [<- one_mul (ENNReal.ofReal _)]
      apply mul_le_mul
      · apply ENNReal.div_self_le_one
      · apply le_trans
        · apply H2
          apply Neighbour.Update
          · simp; rfl
          · simp; rfl
        · apply Hlem2
      · simp
      · simp
    · rw [<- one_add_one_eq_two, add_mul]
      simp
      rw [exp_add]
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => exact exp_nonneg (max ε₁.toReal ε₂.toReal)
      apply mul_le_mul
      · apply le_trans ?G1 _
        case G1 =>
          apply H1
          apply Neighbour.Addition
          · rfl
          · simp; rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
      · apply le_trans ?G1 _
        case G1 =>
          apply H2
          apply Neighbour.Deletion
          · simp; rfl
          · rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
      · simp
      · simp
    · rw [<- one_add_one_eq_two, add_mul]
      simp
      rw [exp_add]
      rw [ENNReal.ofReal_mul ?G1]
      case G1 => exact exp_nonneg (max ε₁.toReal ε₂.toReal)
      apply mul_le_mul
      · apply le_trans ?G1 _
        case G1 =>
          apply H1
          apply Neighbour.Deletion
          · simp; rfl
          · rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
      · apply le_trans ?G1 _
        case G1 =>
          apply H2
          apply Neighbour.Addition
          · rfl
          · simp; rfl
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_monotone
        simp
      · simp
      · simp
    · conv=>
        rhs
        rw [<- mul_one (ENNReal.ofReal _)]
      apply mul_le_mul
      · apply le_trans
        · apply H1
          apply Neighbour.Update
          · simp; rfl
          · simp; rfl
        · apply Hlem1
      · apply ENNReal.div_self_le_one
      · simp
      · simp

theorem pureDP_priv_Par {m1 : Mechanism T U} {m2 : Mechanism T V} {ε₁ ε₂ ε: NNReal} :
    ε = 2 * max ε₁ ε₂ -> ∀f, DP m1 ε₁ -> DP m2 ε₂ -> DP (privParComp m1 m2 f) ε :=
  (· ▸ privParComp_DP_Bound)

end SLang
