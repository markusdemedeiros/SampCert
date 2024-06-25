/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan, Markus de Medeiros
-/

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Logarithm on ENNReal

In this file we extend the logarithm to ``ENNReal``.
-/

noncomputable section

open scoped Classical
open ENNReal EReal Real

namespace ENNReal

/--
Coerce a EReal to an ENNReal by truncation
-/
noncomputable def ofEReal (e : EReal) : ENNReal :=
  match e with
  | ⊥ => some 0
  | ⊤ => ⊤
  | some (some r) => ENNReal.ofReal r

lemma EReal_cases (w : EReal) : w = ⊥ ∨ w = ⊤ ∨ (∃ v : ℝ,  w = v) := by
  cases w
  · left
    rfl
  rename_i w'
  cases w'
  · right
    left
    rfl
  rename_i wR
  right
  right
  exists wR


@[simp]
lemma ofEReal_bot : ofEReal ⊥ = 0 := by simp [ofEReal]

@[simp]
lemma ofEReal_top : ofEReal ⊤ = ⊤ := by simp [ofEReal]

@[simp]
lemma ofEReal_zero : ofEReal 0 = 0 := by simp [ofEReal]


@[simp]
lemma ofEReal_real (r : ℝ) : ofEReal r = ENNReal.ofReal r := by
  simp [Real.toEReal]
  simp [ofEReal]

lemma ofEReal_nonpos (w : EReal) (HW : w ≤ 0): ofEReal w = 0 := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;> simp_all


-- instance : Coe EReal ENNReal := ⟨ofEReal⟩

/--
The extended logarithm
-/
def elog (x : ENNReal) : EReal :=
  match x with
  | ⊤ => ⊤
  | some r => if r = 0 then ⊥ else Real.log r

/--
The extended exponential

Mathlib's has an extended ``rpow`` function of type ``ℝ≥0∞ → ℝ → ℝ≥0∞``, however we
want the exponent to be of type ``EReal``.
-/
def eexp (y : EReal) : ENNReal :=
  match y with
  | ⊥ => 0
  | ⊤ => ⊤
  | some (some r) => ENNReal.ofReal (Real.exp r)


variable {x y : ENNReal}
variable {w z : EReal}
variable {r : Real}

set_option pp.coercions false

@[simp]
lemma elog_of_pos_real (H : 0 < r) : elog (ENNReal.ofReal r) = Real.log r := by
  rw [elog]
  split
  · simp at *
  · split
    · rename_i r' heq h
      exfalso
      rw [h] at heq
      simp at heq
      linarith
    · rename_i h' r' heq h
      simp_all
      congr
      simp [ENNReal.ofReal] at heq
      rw [<- heq]
      exact (Real.coe_toNNReal r (le_of_lt H))

@[simp]
lemma elog_zero : elog (ENNReal.ofReal 0) = ⊥ := by simp [elog]

@[simp]
lemma elog_top : elog ⊤ = ⊤ := by simp [elog]

@[simp]
lemma eexp_bot : eexp ⊥ = 0 := by simp [eexp]

@[simp]
lemma eexp_top : eexp ⊤ = ⊤ := by simp [eexp]

@[simp]
lemma eexp_zero : eexp 0 = 1 := by simp [eexp]

@[simp]
lemma eexp_ofReal : eexp r = ENNReal.ofReal (Real.exp r) := by
  simp [ENNReal.ofReal, eexp, elog]
  rfl

@[simp]
lemma elog_eexp : eexp (elog x) = x := by
  rw [elog]
  split
  · simp
  · rename_i _ r'
    split
    · simp
      rename_i _ h
      rw [h]
    · rename_i _ H
      simp
      rw [NNReal.toReal]
      simp
      rw [Real.exp_log]
      rw [ofReal_coe_nnreal]
      rcases r' with ⟨ v , Hv ⟩
      apply lt_of_le_of_ne
      · simpa
      · simp
        intro Hk
        apply H
        apply NNReal.coe_eq_zero.mp
        simp
        rw [Hk]

@[simp]
lemma eexp_elog : (elog (eexp w)) = w := by
  cases w
  · simp [eexp, elog]
    rfl
  · simp [eexp, elog]
    rename_i v'
    cases v'
    · simp
      rfl
    · simp
      rename_i v''
      simp [ENNReal.ofReal]
      split
      · rename_i Hcont
        have Hcont' : 0 < rexp v'' := by exact exp_pos v''
        linarith
      · rename_i H
        have RW : (max (rexp v'') 0) = (rexp v'') := by
          apply max_eq_left_iff.mpr
          linarith
        simp [RW]
        clear RW
        simp [Real.toEReal]


@[simp]
lemma elog_mul : elog x + elog y = elog (x * y) := by
  rcases x with _ | ⟨ rx , Hrx ⟩ <;>
  rcases y with _ | ⟨ ry , Hry ⟩ <;>
  simp_all
  · rcases (LE.le.lt_or_eq Hry) with Hry' | Hry'
    · simp [elog]
      split
      · exfalso
        rename_i h
        cases h
        linarith
      · simp_all
    · simp [top_mul']
      split
      · simp_all [elog]
      · exfalso
        rename_i H
        apply H
        congr
        rw [Hry']
  · rcases (LE.le.lt_or_eq Hrx) with Hrx' | Hrx'
    · simp [elog]
      split
      · exfalso
        rename_i h
        cases h
        linarith
      · simp_all
    · simp [mul_top']
      split
      · simp_all [elog]
      · exfalso
        rename_i H
        apply H
        congr
        rw [Hrx']
  · rcases (LE.le.lt_or_eq Hry) with Hry' | Hry' <;>
    rcases (LE.le.lt_or_eq Hrx) with Hrx' | Hrx'
    · rw [ENNReal.ofNNReal]
      simp_all [elog]
      sorry
    · sorry
    · simp [elog]
      split
      · rename_i H
        rw [H]
        simp
      · rename_i H
        split
        · rename_i H'
          rw [H']
          simp
        · split
          · exfalso
            simp_all [or_self]
          · simp_all
            sorry
    · simp [elog]
      split
      · split
        · rename_i H1 H2
          rw [H1]
          simp
        · exfalso
          rename_i H
          apply H
          congr
          rw [Hry']
      · exfalso
        rename_i H
        apply H
        congr
        rw [Hrx']


@[simp]
lemma eexp_add : eexp w * eexp z = eexp (w + z) := by sorry -- checked truth table



-- Log of power, log and exp inverses

lemma eexp_injective : eexp w = eexp z -> w = z := by
  rw [eexp, eexp]
  intro H
  cases w <;> cases z <;> try tauto
  · rename_i v
    cases v <;> simp at *
    rename_i v'
    have Hv' := exp_pos v'
    linarith
  · rename_i v
    cases v <;> simp at *
    rename_i v'
    have Hv' := exp_pos v'
    linarith
  · rename_i v₁ v₂
    cases v₁ <;> cases v₂ <;> simp at *
    congr
    rename_i v₁' v₂'
    simp [ENNReal.ofReal] at H
    apply NNReal.coe_inj.mpr at H
    simp at H
    have RW (r : ℝ) : (max (rexp r) 0) = (rexp r) := by
      apply max_eq_left_iff.mpr
      exact exp_nonneg r
    rw [RW v₁'] at H
    rw [RW v₂'] at H
    exact exp_eq_exp.mp H


lemma elog_injective : elog x = elog y -> x = y := by
  rw [elog, elog]
  cases x <;> cases y <;> try tauto
  · rename_i v
    cases v; simp at *

    sorry
  · rename_i v
    cases v; simp at *
    sorry
  · rename_i v₁ v₂
    cases v₁; cases v₂; simp at *
    sorry

lemma eexp_mono_lt : (w < z) <-> eexp w < eexp z := by
  sorry

lemma eexp_mono_le : (w <= z) <-> eexp w <= eexp z := by sorry

lemma elog_mono_lt : (x < y) <-> elog x < elog y := by sorry

lemma elog_mono_le : (x <= y) <-> elog x <= elog y := by sorry

-- iff for log positive

-- Special values

-- Need to write compat lemmas for ofEReal
-- Not sure which ones we'll need but


-- Specialized lemmas for ofEReal when its argument is nonnegative (so no truncation happens)
lemma ofEReal_nonneg_eq_iff (Hw : 0 <= w) (Hz : 0 <= z) : w = z <-> (ofEReal w = ofEReal z) := by
  apply Iff.intro
  · intro H1
    rw [H1]
  · intro H1
    rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
    rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩) <;>
    simp_all

lemma ofEReal_le_mono_nonneg (Hw : 0 ≤ w) : w ≤ z <-> (ofEReal w ≤ ofEReal z) := by
  apply Iff.intro
  · intro H1
    rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
    rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩) <;>
    simp_all
    exact ofReal_le_ofReal H1
  · intro H1
    rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
    rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩) <;>
    simp_all
    · sorry
    · simp [ENNReal.ofReal] at H1
      apply toNNReal_le_toNNReal_iff'.mp at H1
      cases H1
      · assumption
      · rename_i H
        have H' : w' = 0 := by apply le_antisymm <;> assumption
        simp_all
        apply EReal.coe_nonneg.mp
        simp_all
        -- ???
        sorry

-- Use above
lemma ofEReal_nonneg_zero (Hz : 0 ≤ z) : (0 = z) <-> 0 = ofEReal z := sorry


lemma ofEReal_le_mono (H : w ≤ z) : ofEReal w ≤ ofEReal z := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
  rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩)
  all_goals rw [Hw', Hz']
  all_goals simp_all [ENNReal.ofEReal]
  simp [Real.toEReal]
  exact ofReal_le_ofReal H


@[simp]
lemma ofEReal_plus_nonneg (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w + z) = ofEReal w + ofEReal z := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
  rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩)
  all_goals rw [Hw', Hz']
  all_goals simp_all
  sorry

@[simp]
lemma ofEReal_mul_nonneg (Hw : 0 ≤ w) (Hz : 0 ≤ z) : ofEReal (w * z) = ofEReal w * ofEReal z := by
  have HBle: (⊥ : EReal) ≤ 0 := by exact OrderBot.bot_le 0
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
  rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩)
  all_goals rw [Hw', Hz']
  all_goals simp_all
  · rw [top_mul']
    split
    · simp_all
      apply ofEReal_nonpos
      sorry
    · cases (LE.le.lt_or_eq Hz)
      · sorry
      · sorry
  · sorry
  · sorry

lemma ofEReal_nonneg_scal_l (H1 : 0 < r) (H2 : 0 ≤ r * w) : 0 ≤ w := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩)
  · simp_all
    rw [EReal.mul_bot_of_pos] at H2
    all_goals simp_all
  · simp_all
  · simp_all
    sorry


@[simp]
lemma toEReal_ofENNReal_nonneg (H : 0 ≤ w) : ENNReal.toEReal (ofEReal w) = w := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;> simp_all


@[simp]
lemma ofEReal_toENNReal : ofEReal (ENNReal.toEReal x) = x := by
  rw [ENNReal.ofEReal]
  split
  · rename_i x' Hx'
    simp [toEReal] at Hx'
    cases x <;> simp_all
    rename_i x''
    exfalso
    rw [NNReal.toReal] at Hx'
    rw [Real.toEReal] at Hx'
    simp_all
  · rename_i x' Hx'
    simp [toEReal] at Hx'
    cases x <;> simp_all
    rw [NNReal.toReal] at Hx'
    rw [Real.toEReal] at Hx'
    simp_all
    cases Hx'
  · rename_i e x' Hx'
    simp [toEReal] at Hx'
    cases x <;> simp_all
    · cases Hx'
    · rw [ENNReal.ofReal]
      simp_all
      rw [NNReal.toReal] at Hx'
      rw [Real.toEReal] at Hx'
      simp_all
      cases Hx'
      simp_all

lemma ofEReal_ofReal_toENNReal : ENNReal.ofEReal (Real.toEReal r) = ENNReal.ofReal r := by
  simp [ofEReal, Real.toEReal, ENNReal.ofReal]

set_option pp.coercions false

lemma elog_ENNReal_ofReal_of_pos (x : ℝ) (H : 0 < x): (ENNReal.ofReal x).elog = x.log.toEReal := by
  simp [ENNReal.ofReal, ENNReal.elog, ENNReal.toEReal]
  rw [ite_eq_iff']
  apply And.intro
  · intro
    exfalso
    linarith
  · intro H
    simp at H
    rw [max_eq_left_of_lt H]


-- ENNReal inequalities
-- These are needed to prove the extensded version of Jensen's inequality
lemma mul_mul_inv_le_mul_cancel : (x * y⁻¹) * y ≤ x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  simp
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

lemma mul_mul_inv_eq_mul_cancel (H : y = 0 -> x = 0) (H2 : ¬(x ≠ 0 ∧ y = ⊤)) : (x * y⁻¹) * y = x := by
  cases x
  · simp_all
  rename_i x'
  cases (Classical.em (x' = 0))
  · simp_all
  rename_i Hx'
  cases y
  · simp_all
  rename_i y'
  cases (Classical.em (y' = 0))
  · simp_all
  rename_i Hy'
  simp
  rw [← coe_inv Hy']
  rw [← coe_mul]
  rw [← coe_mul]
  rw [mul_right_comm]
  rw [mul_inv_cancel_right₀ Hy' x']

-- Could be shortened
lemma ereal_smul_le_left (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w ≤ s * z) : w ≤ z := by
  have defTop : some none = (⊤ : EReal) := by simp [Top.top]
  have defBot : none = (⊥ : EReal) := by simp [Bot.bot]

  cases s
  · exfalso
    rw [defBot] at Hr1
    simp_all only [not_lt_bot]
  rename_i s_nnr
  cases s_nnr
  · rw [defTop] at Hr2
    exfalso
    simp_all only [EReal.zero_lt_top, lt_self_iff_false]
  rename_i s_R
  have Hsr : some (some s_R) = Real.toEReal s_R := by simp [Real.toEReal]
  rw [Hsr] at H
  rw [Hsr] at Hr1
  rw [Hsr] at Hr2
  clear Hsr

  cases w
  · apply left_eq_inf.mp
    rfl
  rename_i w_nnr
  cases w_nnr
  · simp [defTop] at H
    rw [EReal.mul_top_of_pos Hr1] at H
    have X1 : z = ⊤ := by
      cases z
      · exfalso
        simp at H
        rw [defBot] at H
        rw [EReal.mul_bot_of_pos] at H
        · cases H
        · apply Hr1
      rename_i z_nnr
      cases z_nnr
      · simp [Top.top]
      exfalso
      apply top_le_iff.mp at H
      rename_i z_R
      have Hzr : some (some z_R) = Real.toEReal z_R := by simp [Real.toEReal]
      rw [Hzr] at H
      rw [<- EReal.coe_mul] at H
      cases H
    rw [defTop, X1]
  rename_i w_R
  cases z
  · simp [defBot] at H
    rw [EReal.mul_bot_of_pos] at H
    apply le_bot_iff.mp at H
    · rw [defBot]
      have Hwr : some (some w_R) = Real.toEReal w_R := by simp [Real.toEReal]
      rw [Hwr] at H
      rw [<- EReal.coe_mul] at H
      cases H
    · apply Hr1
  rename_i z_nnr
  cases z_nnr
  · exact right_eq_inf.mp rfl
  rename_i z_R
  have Hwr : some (some w_R) = Real.toEReal w_R := by simp [Real.toEReal]
  have Hzr : some (some z_R) = Real.toEReal z_R := by simp [Real.toEReal]
  rw [Hwr, Hzr] at H
  rw [Hwr, Hzr]
  clear Hwr
  clear Hzr
  apply EReal.coe_le_coe_iff.mpr
  repeat rw [<- EReal.coe_mul] at H
  apply EReal.coe_le_coe_iff.mp at H
  apply le_of_mul_le_mul_left H
  exact EReal.coe_pos.mp Hr1

lemma ereal_smul_eq_left (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : s * w = s * z) : w = z := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
  rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩) <;>
  rcases (EReal_cases s) with Hs' | (Hs' | ⟨ s', Hs' ⟩)
  all_goals rw [Hw', Hz']
  all_goals simp_all
  · rw [mul_top_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    rw [mul_bot_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    cases H
  · rw [mul_bot_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    cases H
  · rw [mul_top_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    rw [mul_bot_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    cases H
  · rw [mul_top_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    cases H
  · rw [mul_bot_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    repeat rw [<- EReal.coe_mul] at H
    cases H
  · rw [mul_top_of_pos (by exact EReal.coe_pos.mpr Hr1)] at H
    repeat rw [<- EReal.coe_mul] at H
    cases H
  · repeat rw [<- EReal.coe_mul] at H
    apply EReal.coe_eq_coe_iff.mp at H
    simp_all only [mul_eq_mul_left_iff]
    cases H
    · assumption
    · exfalso
      linarith

lemma ereal_smul_left_le (s : EReal) (Hr1 : 0 < s) (Hr2 : s < ⊤) (H : w ≤ z) : s * w ≤ s * z := by
  rcases (EReal_cases w) with Hw' | (Hw' | ⟨ w', Hw' ⟩) <;>
  rcases (EReal_cases z) with Hz' | (Hz' | ⟨ z', Hz' ⟩)
  all_goals rw [Hw', Hz']
  all_goals simp_all
  · rw [mul_top_of_pos Hr1]
    exact OrderTop.le_top (s * ⊥)
  · rw [mul_bot_of_pos Hr1]
    exact OrderBot.bot_le (s * z'.toEReal)
  · rw [mul_top_of_pos Hr1]
    exact OrderTop.le_top (s * w'.toEReal)
  rcases (EReal_cases s) with Hs' | (Hs' | ⟨ s', Hs' ⟩)
  all_goals simp_all
  repeat rw [← EReal.coe_mul]
  apply EReal.coe_le_coe_iff.mpr
  exact (mul_le_mul_iff_of_pos_left Hr1).mpr H

lemma ENNReal_toReal_partial_inj (a b : ENNReal) (H : a.toReal = b.toReal) (H1 : a ≠ ⊤) (H2 : b ≠ ⊤) : a = b := by
  rcases a with Ha' | ⟨ a' | Ha' ⟩ <;>
  rcases b with Hb' | ⟨ b' | Hb' ⟩
  all_goals simp_all

end ENNReal
