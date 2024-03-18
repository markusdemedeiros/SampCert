/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.Foundations.Basic
import SampCert.Samplers.Uniform
import SampCert.Samplers.Bernoulli
import Mathlib.Data.Complex.Exponential

open PMF Nat BigOperators Finset

theorem halve_wf (num : Nat) (den st : PNat) (wf : num ≤ den) :
  num ≤ ↑(st * den) := by
  simp
  cases st
  rename_i v p
  simp
  exact le_mul_of_one_le_of_le p wf

noncomputable def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den) (state : (Bool × PNat)) : RandomM (Bool × PNat) := do
  let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
  return (A, state.2 + 1)

noncomputable def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Nat := do
  let r ← prob_while (λ state : Bool × PNat => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
  return r.2

@[simp]
theorem BernoulliExpNegSampleUnitAux_zero (num : ℕ) (den : ℕ+) (st st' : Bool × ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) 0 st st' = 0 := by
  simp [prob_while_cut]

@[simp]
theorem BernoulliExpNegSampleUnitAux_returns_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (true, r) = 0 := by
  revert st r
  induction fuel
  . simp [prob_while_cut]
  . rename_i fuel IH
    intro st r
    simp [prob_while_cut, WhileFunctional]
    unfold SubPMF.bind
    unfold SubPMF.pure
    simp [ite_apply]
    split
    . rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      conv =>
        left
        right
        intro a
        rw [IH a r]
      simp
    . rename_i h
      cases st
      rename_i b n
      simp at h
      subst h
      simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_ite_simpl (x r : ℕ+) (k : ENNReal) :
  @ite ENNReal (x = r + 1) (Classical.propDecidable (x = r + 1)) 0
  (@ite ENNReal (x = r + 1) (instPNatDecidableEq x (r + 1)) k 0) = 0 := by
  split
  . simp
  . simp

@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_true (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (true, r) st =
    (num / (r * den)) * prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (true, r + 1) st
    + (1 - (num / (r * den))) * prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel (false, r + 1) st := by
  cases st
  rename_i b' r'
  simp [prob_while_cut, WhileFunctional, ite_apply, ENNReal.tsum_prod', tsum_bool, BernoulliExpNegSampleUnitLoop]
  conv =>
    left
    congr
    . rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]
    . rw [ENNReal.tsum_eq_add_tsum_ite (r + 1)]
      right
      right
      intro x
      rw [BernoulliExpNegSampleUnitAux_ite_simpl]
  simp
  rw [add_comm]


@[simp]
theorem BernoulliExpNegSampleUnitAux_succ_false (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (r : ℕ+) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (succ fuel) (false, r) st =
  if st = (false,r) then 1 else 0 := by
  cases st
  simp [prob_while_cut, WhileFunctional]

@[simp]
theorem BernoulliExpNegSampleUnitAux_monotone_counter (num : ℕ) (den : ℕ+) (fuel : ℕ) (st : Bool × ℕ+) (n : ℕ+) (wf : num ≤ den)  (h1 : st ≠ (false,n)) (h2 : st.2 ≥ n) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) fuel st (false, n) = 0 := by
  revert st
  induction fuel
  . simp
  . rename_i fuel IH
    intro st h1 h2
    cases st
    rename_i stb stn
    simp at h1
    simp at h2
    cases stb
    . simp
      exact Ne.symm (h1 rfl)
    . simp [BernoulliExpNegSampleUnitAux_succ_true]
      have A : (false, stn + 1) ≠ (false, n) := by
        simp
        have OR : n = stn ∨ n < stn := by exact eq_or_lt_of_le h2
        cases OR
        . rename_i h
          subst h
          exact _root_.ne_of_gt le.refl
        . rename_i h
          exact _root_.ne_of_gt (le.step h)
      have B : (true, stn + 1) ≠ (false, n) := by exact
        (bne_iff_ne (true, stn + 1) (false, n)).mp rfl
      rw [IH _ A]
      rw [IH _ B]
      simp
      exact le.step h2
      exact le.step h2

-- The following two functions are useful to keep the dependent definition of PNat under control
-- Otherwise, the terms become large and unreadable

def plus_one (k : ℕ) : ℕ+ := ⟨ k + (1 : ℕ+) , Nat.add_pos_right k le.refl ⟩

def plus_two (k fuel : ℕ) : ℕ+ := ⟨ fuel + k + 2 , Nat.add_pos_right (fuel + k) (le.step le.refl) ⟩

@[simp]
theorem plus_one_p1 (k e : ℕ) :
  plus_one k + e = plus_one (k + e) := by
  simp [plus_one]
  conv =>
    right
    rw [add_assoc]
    right
    rw [add_comm]
  conv =>
    right
    rw [← add_assoc]

theorem plus_one_prop (k : ℕ) :
  plus_one k = k + 1 := by
  simp [plus_one]

theorem plus_two_zero_prop (k : ℕ) :
  plus_two k 0 = k + 2 := by
  simp [plus_two]

theorem nm2p2 (n : ℕ) (h : n > 1) :
  n - 2 + 2 = n := by
  exact Nat.sub_add_cancel h

-- Warning! BernoulliExpNegSampleUnitAux has a transition phase
-- This min is suspicious: (min (fuel + 2) (fuel + k + 1) - 2)
@[simp]
theorem BernoulliExpNegSampleUnitAux_progress (num : ℕ) (den : ℕ+) (fuel k : ℕ) (wf : num ≤ den) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel ) = (∏ i in range fuel, (num : ENNReal) / ((k + 1 + i) * den)) * (1 - ((num : ENNReal) / ((fuel + k + 1) * den))) := by
  revert k
  induction fuel
  . intro k
    simp
    split
    . rename_i h
      rw [plus_one_prop]
      simp
    . rename_i h
      have A : ¬ k + 2 = k + 2 := by
        conv =>
          right
          congr
          . rw [← plus_two_zero_prop]
          . change k + (1 + 1)
            rw [← add_assoc]
            rw [← plus_one_prop]
        refine (Function.Injective.ne_iff ?hf).mpr h
        exact PNat.coe_injective
      contradiction
  . rename_i fuel IH
    intro k
    rw [BernoulliExpNegSampleUnitAux_succ_true]
    rw [BernoulliExpNegSampleUnitAux_succ_false]
    have IH' := IH (k + 1)
    clear IH
    have A : plus_one (k + 1) = plus_one k + 1 := rfl
    have B : plus_two (k + 1) fuel = plus_two k (succ fuel) := by
      simp [plus_two]
      have X : fuel + (k + 1) + 2 = succ fuel + k + 2 := by
        conv =>
          left
          left
          right
          rw [add_comm]
        rw [← add_assoc]
      conv =>
        left
        left
        rw [X]
    rw [← A]
    rw [← B]
    rw [IH']
    have C : ¬ plus_two (k + 1) fuel = plus_one (k + 1) := by
      by_contra
      rename_i h
      simp [plus_one, plus_two] at h
      cases h
    simp [C]
    have E : fuel + (k + (1 : ENNReal)) + (1 : ENNReal) = ↑fuel + 1 + ↑k + 1 := by -- duplicate later on
      conv =>
        left
        left
        right
        rw [add_comm]
      rw [← add_assoc]
    rw [E]
    clear IH' A B C E
    simp [prod_range_succ']
    rw [plus_one_prop]
    conv =>
      right
      left
      rw [mul_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      right
      rw [add_comm]
    conv =>
      right
      left
      right
      right
      intro x
      right
      left
      rw [← add_assoc]
    simp
    rw [mul_assoc]

theorem adhoc (n : ℕ) (h : n > 1) :
  n - 2 + 1 = n - 1 := by
  rw [← tsub_tsub_assoc]
  . exact h
  . exact le.step le.refl

theorem adhoc' (n : ℕ) (h : n > 1) :
  (n : ENNReal) - 2 + 1 = (n : ENNReal) - 1 := by
  have C := @congrArg ℕ ENNReal (n - 2 + 1) (n - 1) Nat.cast  (adhoc n h)
  simp at C
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_progress' (num : ℕ) (den : ℕ+) (n : ℕ) (wf : num ≤ den) (h : n > 1) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1 ) (false, ⟨ n , lt_of_succ_lt h ⟩ ) = (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  have prog := BernoulliExpNegSampleUnitAux_progress num den (n - 2) 0 wf
  have A := nm2p2 n h
  rw [A] at prog
  have B : plus_two 0 (n - 2) = ⟨ n , lt_of_succ_lt h ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [A]
  rw [B] at prog
  simp [plus_one] at prog
  have C := adhoc' n h
  rw [C] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation (num : ℕ) (den : ℕ+) (fuel fuel' k : ℕ) (wf : num ≤ den) (h1 : fuel ≥ fuel') :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (1 + fuel + 2) (true, plus_one k ) (false, plus_two k fuel')
    = prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (fuel + 2) (true, plus_one k ) (false, plus_two k fuel') := by
  revert fuel' k
  induction fuel
  . intro fuel' k h1
    have A : fuel' = 0 := by exact le_zero.mp h1
    subst A
    simp [BernoulliExpNegSampleUnitAux_succ_true]
    -- rewrites of plus_* properties do not work because the type is wrong
    have B : ¬ plus_two k 0 = plus_one k + 1 + 1 := by
      simp [plus_two, plus_one]
      by_contra
      rename_i h
      cases h -- similar proof in BernoulliExpNegSampleUnitAux_progress
    simp [B]
  . rename_i fuel IH
    intro fuel' k h1
    conv =>
      congr
      . rw [BernoulliExpNegSampleUnitAux_succ_true]
      . rw [BernoulliExpNegSampleUnitAux_succ_true]
    have A : succ fuel + 1 = fuel + 2 := by exact rfl
    rw [A]
    have B : 1 + succ fuel + 1 = 1 + fuel + 2 := by exact rfl
    rw [B]
    have Pre : fuel ≥ fuel' - 1 := by exact sub_le_of_le_add h1
    have IH' := IH (fuel' - 1) (k + 1) Pre
    clear IH
    cases fuel'
    . rw [BernoulliExpNegSampleUnitAux_succ_false]
      rw [BernoulliExpNegSampleUnitAux_succ_false]
      have C : plus_two k zero = plus_one k + 1 := by   -- Useful for cleanup
        simp [plus_two, plus_one]
        rfl
      rw [C]
      simp
    . rename_i fuel'
      have C : succ fuel' - 1 = fuel' := by exact rfl
      rw [C] at IH'
      have D : plus_two (k + 1) fuel' = plus_two k (succ fuel') := by -- Important example for cleanup
        simp [plus_two]
        have X : fuel' + (k + 1) + 2 = succ fuel' + k + 2 := by
          conv =>
            left
            left
            right
            rw [add_comm]
          rw [← add_assoc]
        conv =>
          left
          left
          rw [X]
      rw [D] at IH'
      have E : plus_one (k + 1) = plus_one k + 1 := by  -- Useful for cleanup
        simp [plus_one]
        rfl
      rw [E] at IH'
      rw [IH']
      exact rfl

@[simp]
theorem BernoulliExpNegSampleUnitAux_preservation' (num : ℕ) (den : ℕ+) (n m : ℕ) (wf : num ≤ den) (h1 : m > 1) (h2 : n ≥ m) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (n + 1) (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩ )
    = prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) n (true, 1) (false, ⟨ m, zero_lt_of_lt h1 ⟩) := by
  have X : n - 2 ≥ m - 2 := by exact Nat.sub_le_sub_right h2 2
  have prog := BernoulliExpNegSampleUnitAux_preservation num den (n - 2) (m - 2) 0 wf X
  have A : 1 + (n - 2) + 2 = n + 1 := by
    rw [add_assoc]
    rw [add_comm]
    rw [_root_.add_left_inj]
    rw [nm2p2 n (Nat.lt_of_lt_of_le h1 h2)]
  have B := nm2p2 n (Nat.lt_of_lt_of_le h1 h2)
  have C : plus_one 0 = 1 := by
    simp [plus_one]
  have D : plus_two 0 (m - 2) = ⟨ m, zero_lt_of_lt h1 ⟩ := by
    simp [plus_two]
    conv =>
      left
      left
      rw [nm2p2 m h1]
  rw [A, B, C, D] at prog
  trivial

@[simp]
theorem BernoulliExpNegSampleUnitAux_characterization (num : ℕ) (den : ℕ+) (n extra : ℕ) (wf : num ≤ den) (h : n > 1) :
  prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) (extra + n) (true, 1) (false, ⟨ n, by exact zero_lt_of_lt h ⟩)
    =  (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  revert n
  induction extra
  . simp
    intro n h
    apply BernoulliExpNegSampleUnitAux_progress' num den n wf h
  . rename_i extra IH
    intro n h
    have IH' := IH n h
    clear IH
    rw [← BernoulliExpNegSampleUnitAux_preservation'] at IH'
    . have B : extra + n + 1 = succ extra + n := by
        clear IH'
        clear IH'
        conv =>
          left
          rw [add_comm]
          rw [← add_assoc]
        rw [add_left_inj]
        exact one_add extra
      rw [← B]
      trivial
    . trivial
    . exact Nat.le_add_left n extra

theorem BernoulliExpNegSampleUnitAux_sup (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  ⨆ i, prob_while_cut (fun state => state.1) (BernoulliExpNegSampleUnitLoop num den wf) i (true, 1) (false, n)
    = if n = 1 then 0 else (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  apply iSup_eq_of_tendsto
  . apply prob_while_cut_monotonic
  . rw [Iff.symm (Filter.tendsto_add_atTop_iff_nat n)]
    split
    . rename_i h
      subst h
      rw [ENNReal.tendsto_atTop_zero]
      intro ε _
      existsi 0
      intro n _
      simp [BernoulliExpNegSampleUnitAux_monotone_counter]
    . rename_i h
      have h' : n > 1 := by
        by_contra
        rename_i h'
        simp at *
        subst h'
        contradiction
      have FOO (n_1 : ℕ) := @BernoulliExpNegSampleUnitAux_characterization num den n n_1 wf h'
      have BAR : n = (@Subtype.mk.{1} Nat (fun (n : Nat) => @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)
          (PNat.val n) (@Nat.zero_lt_of_lt (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (PNat.val n) h')) := rfl
      conv =>
        congr
        intro n_1
        right
        rw [BAR]
      conv =>
        congr
        intro E
        rw [FOO E]
      rw [tendsto_const_nhds_iff]

theorem if_simpl' (num : ℕ) (den : ℕ+) (x n : ℕ+) :
  @ite ENNReal (x = n) (Classical.propDecidable (x = n)) 0
  (@ite ENNReal (n = x) (instPNatDecidableEq n x)
  (@ite ENNReal (x = 1) (instPNatDecidableEq x 1) 0
  ((∏ i in range (↑x - 2), ↑num / (((1 : ENNReal) + ↑i) * ↑↑den)) * (1 - ↑num / ((↑↑x - 1) * ↑↑den)))) 0) = 0 := by
  split
  . simp
  . split
    . split
      . simp
      . rename_i h1 h2 h3
        subst h2
        contradiction
    . simp

theorem BernoulliExpNegSampleUnitAux_apply (num : ℕ) (den : ℕ+) (n : ℕ+) (wf : num ≤ den) :
  (BernoulliExpNegSampleUnitAux num den wf) n =
    if n = 1 then 0 else (∏ i in range (n - 2), (num : ENNReal) / ((1 + i) * den)) * (1 - ((num : ENNReal) / ((n - 1) * den))) := by
  simp [BernoulliExpNegSampleUnitAux]
  rw [ENNReal.tsum_prod']
  rw [tsum_bool]
  simp [prob_while]
  simp [BernoulliExpNegSampleUnitAux_sup]
  rw [ENNReal.tsum_eq_add_tsum_ite n]
  simp
  conv =>
    left
    right
    right
    intro x
    rw [if_simpl']
  simp

-- @[simp]
-- theorem BernoulliExpNegSampleUnitAux_apply' (num : Nat) (den : PNat) (wf : num ≤ den) (n : Nat) (gam : γ = (num : ℝ) / (den : ℝ)) :
--   (BernoulliExpNegSampleUnitAux num den wf) n =
--   ENNReal.ofReal ((γ^(n - 1) / (factorial (n - 1))) - (γ^n / (factorial n))) := by
--   sorry

noncomputable def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : RandomM Bool := do
  let K ← BernoulliExpNegSampleUnitAux num den wf
  if K % 2 = 0 then return true else return false

-- @[simp]
-- theorem BernoulliExpNegSampleUnit_apply_false (num : Nat) (den : PNat)  (wf : num ≤ den) (gam : γ = (num : ℝ) / (den : ℝ)) :
--   (BernoulliExpNegSampleUnit num den wf) false = ENNReal.ofReal (Real.exp (- γ)) := by
--   have B : Real.exp (-γ) ≥ 0 := by exact Real.exp_nonneg (-γ)
--   simp [BernoulliExpNegSampleUnit]
--   unfold SubPMF.pure
--   simp [ite_apply]
--   conv =>
--     left
--     right
--     intro a
--     rw [BernoulliExpNegSampleUnitAux_apply' num den wf a gam]
--   have C : (∑' (a : ℕ), if a % 2 = 0 then 0 else ENNReal.ofReal (γ ^ (a - 1) / ↑(a - 1)! - γ ^ a / ↑a !))
--     = (∑' (a : ℕ), ENNReal.ofReal ((-γ)^a / (a - 1)!)) := by sorry
--   rw [C]
--   sorry -- need to connect to definition of exp

-- @[simp]
-- theorem BernoulliExpNegSampleUnit_apply_true (num : Nat) (den : PNat)  (wf : num ≤ den) (gam : γ = (num : ℝ) / (den : ℝ)) :
--   (BernoulliExpNegSampleUnit num den wf) true = 1 - ENNReal.ofReal (Real.exp (- γ)) := by
--   sorry

noncomputable def BernoulliExpNegSampleGenLoop (iter : Nat) : RandomM Bool := do
  if iter = 0 then return true
  else
    let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
    if ¬ B then return B else
      let R ← BernoulliExpNegSampleGenLoop (iter - 1)
      return R

noncomputable def BernoulliExpNegSample (num : Nat) (den : PNat) : RandomM Bool := do
  if h : num ≤ den
  then let X ← BernoulliExpNegSampleUnit num den h
       return X
  else
    let gamf := floor (num / den)
    let B ← BernoulliExpNegSampleGenLoop (gamf)
    if B
    then
         let num := num - gamf * den
         let X ← BernoulliExpNegSampleUnit num den sorry
         return X
    else return false

-- @[simp]
-- theorem BernoulliExpNegSample_apply (num : Nat) (den : PNat) (_ : γ = (num : ℝ) / (den : ℝ)) :
--   (BernoulliExpNegSample num den) true = ENNReal.ofReal (Real.exp (-γ)) := sorry
