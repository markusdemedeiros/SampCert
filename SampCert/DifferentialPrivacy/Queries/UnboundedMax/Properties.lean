/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Abstract

noncomputable section
open Classical

namespace SLang


/--
Stronger congruence rule for probBind: The bound-to functions have to be equal only on the support of
the bound-from function.
-/
lemma probBind_congr_strong (p : SLang T) (f : T -> SLang U) (g : T -> SLang U) (Hcong : ∀ t : T, p t ≠ 0 -> f t = g t) :
    p >>= f = p >>= g := by
  simp
  unfold probBind
  apply SLang.ext
  intro u
  apply Equiv.tsum_eq_tsum_of_support ?G1
  case G1 =>
    apply Set.BijOn.equiv (fun x => x)
    simp [Function.support]
    have Heq : {x | ¬p x = 0 ∧ ¬f x u = 0} =  {x | ¬p x = 0 ∧ ¬g x u = 0} := by
      apply Set.sep_ext_iff.mpr
      intro t Ht
      rw [Hcong]
      apply Ht
    rw [Heq]
    apply Set.bijOn_id
  simp [Function.support]
  intro t ⟨ Hp, _ ⟩
  simp [Set.BijOn.equiv]
  rw [Hcong]
  apply Hp


/-
## Helper programs
-/

/--
Sum over a list, clipping each element to a maximum.

Similar to exactBoundedSum, however exactClippedSum allows m = 0.
-/
def exactClippedSum (m : ℕ) (l : List ℕ) : ℤ :=
  List.sum (List.map (fun n : ℕ => (Nat.min n m)) l)

/--
Rate at which a given clipping thresold is impacting the accuracy of the sum.

Always negative or zero.
-/
def exactDiffSum (m : ℕ) (l : List ℕ) : ℤ := exactClippedSum m l - exactClippedSum (m + 1) l

/--
Noise the constant 0 value using the abstract noise function.

This looks strange, but will specialize to Lap(ε₁/ε₂, 0) in the pure DP case.
-/
def privNoiseZero [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) : SLang ℤ := dps.noise (fun _ => 0) 1 ε₁ ε₂ []

/-
Not used for anything, but to give confidence in our definitions

(exactDiffSum l m) is zero if and only if m is an upper bound on the list elements
-/
-- lemma exactDiffSum_eq_0_iff_ge_max (l : List ℕ) (m : ℕ) :
--     l.maximum ≤ m <-> exactDiffSum m l ≤ 0 := by
--   apply Iff.intro
--   · induction l
--     · simp [exactDiffSum, exactClippedSum]
--     · rename_i l0 ls IH
--       intro Hmax
--       simp [List.maximum_cons] at Hmax
--       rcases Hmax with ⟨ Hmax0, Hmax1 ⟩
--       have IH' := IH Hmax1
--       clear IH
--       simp [exactDiffSum, exactClippedSum] at *
--       apply Int.add_le_of_le_neg_add
--       apply le_trans IH'
--       simp
--   · intro H1
--     apply List.maximum_le_of_forall_le
--     revert H1
--     induction l
--     · simp
--     · rename_i l0 ls IH
--       intro Hdiff a Ha
--       rw [List.mem_cons_eq] at Ha
--       cases Ha
--       · rename_i H
--         rw [H]
--         rw [Nat.cast_withBot]
--         apply WithBot.coe_le_coe.mpr
--
--         sorry
--       · apply IH; clear IH
--         · simp only [exactDiffSum, exactClippedSum] at *
--           have H : (min (l0.cast : ℤ) (m.cast : ℤ) - min (l0.cast) ((m.cast : ℤ) + 1)) = 0 := by
--             sorry
--           -- rw [H] at Hdiff
--           -- rw [<- Hdiff]
--           -- simp
--           sorry
--         · trivial


/-
## Program version 0
  - Executable
  - Tracks single state
-/

def sv0_state : Type := ℕ × ℤ

def sv0_threshold (s : sv0_state) : ℕ := s.1

def sv0_noise (s : sv0_state) : ℤ := s.2

def sv0_privMaxC (τ : ℤ) (l : List ℕ) (s : sv0_state) : Bool :=
  decide (exactDiffSum (sv0_threshold s) l + (sv0_noise s) < τ)

def sv0_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv0_state) : SLang sv0_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  let n := (sv0_threshold s) + 1
  return (n, vn)

def sv0_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0)
  return (sv0_threshold sk)

/-
## Program version 1
  - Executable
  - Tracks history of samples
-/

def sv1_state : Type := List ℤ × ℤ

def sv1_threshold (s : sv1_state) : ℕ := List.length s.1

def sv1_noise (s : sv1_state) : ℤ := s.2

def sv1_privMaxC (τ : ℤ) (l : List ℕ) (s : sv1_state) : Bool :=
  decide (exactDiffSum (sv1_threshold s) l + (sv1_noise s) < τ)

def sv1_privMaxF [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (s : sv1_state) : SLang sv1_state := do
  let vn <- @privNoiseZero dps ε₁ (4 * ε₂)
  return (s.1 ++ [s.2], vn)

def sv1_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
  let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
  let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
  return (sv1_threshold sk)

/--
History-aware progam computes the same as the history-agnostic program
-/
lemma sv0_eq_sv1 [dps : DPSystem ℕ] ε₁ ε₂ l : sv0_privMax ε₁ ε₂ l = sv1_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Initial setup is equal
  intro result
  simp [sv0_privMax, sv1_privMax]
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1

  -- unfold sum over product; term re. last sample should be equal as well
  conv =>
    congr
    · unfold sv0_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    · unfold sv1_state
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  apply tsum_congr
  intro vk

  -- LHS: simplify singleton sum
  conv =>
    enter [1, 1, a]
    simp [sv0_threshold]
  rw [ENNReal.tsum_eq_add_tsum_ite result]
  simp
  rw [@tsum_congr ENNReal ℕ _ _ _ (fun _ => 0) ?G1]
  case G1 =>
    intro
    split <;> simp
    rename_i H1
    intro
    exfalso
    apply H1
    symm
    trivial
  simp only [tsum_zero, add_zero]

  -- RHS: sum over all lists of length "result"?
  -- rw [tsum_ite_eq]
  -- simp [sv1_threshold]



  sorry



/-
## Program version 2
  - Only moves the loop into a non-executable form, ie. explicitly defines the PMF
-/

def sv2_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
    return (sv1_threshold sk)
  computation point

lemma sv1_eq_sv2 [dps : DPSystem ℕ] ε₁ ε₂ l : sv1_privMax ε₁ ε₂ l = sv2_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro result
  simp [sv1_privMax, sv2_privMax]




/-
## Program version 3
  - Truncates the loop
-/

def sv3_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  probWhileCut (sv1_privMaxC τ l) (@sv1_privMaxF dps ε₁ ε₂) (point + 1) init

def sv3_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- @sv3_loop dps ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point


def cone_of_possibility (cut : ℕ) (initial hist : List ℤ) : Prop :=
  (hist.length < cut + initial.length) ∧ (initial.length ≤ hist.length)

def constancy_at [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) : Prop :=
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) (1 + cut) (initial, v0) (hist, vk) =
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut       (initial, v0) (hist, vk)


-- All points outside of the cone are zero
lemma external_to_cone_zero [DPSystem ℕ] :
    (¬ cone_of_possibility cut initial hist) ->
    probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut (initial, v0) (hist, vk) = 0 := by
  revert initial v0 vk
  induction cut
  · simp [probWhileCut, probWhileFunctional]
  · rename_i cut' IH
    intro intial v0 vk Hcut'
    unfold probWhileCut
    unfold probWhileFunctional
    split <;> simp
    · intro h
      rcases h with ⟨ initial', vk' ⟩
      cases Classical.em (¬ ∃ v', initial' = intial  ++ [v'])
      · left
        simp [sv1_privMaxF]
        intro i Hi
        exfalso
        cases Hi
        rename_i h
        apply h
        exists v0
      rename_i h
      simp at h
      rcases h with ⟨ v', Hinitial' ⟩
      right
      apply IH
      simp_all [cone_of_possibility]
      intro
      have Hcut'' := Hcut' (by linarith)
      linarith
    · intro H
      cases H
      simp_all [cone_of_possibility]

-- Base case: left edge of the cone satisfies constancy
lemma cone_left_edge_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
  intro Hlen Hcone
  -- cut > 0 due to cone
  cases cut
  · exfalso
    simp [cone_of_possibility] at Hcone
    simp_all only [lt_self_iff_false, le_refl, and_true]
  rename_i cut'

  -- Unfold the first iterate
  unfold constancy_at
  unfold probWhileCut
  unfold probWhileFunctional

  cases (sv1_privMaxC τ data (initial, v0))
  · -- False case: both programs terminate with initial state
    simp
  · -- True case: both programs step to a point outside of the cone, so are zero
    simp
    apply tsum_congr
    intro ⟨ initial', v1 ⟩

    simp [sv1_privMaxF]
    rw [← ENNReal.tsum_mul_right]
    rw [← ENNReal.tsum_mul_right]

    -- Ignore the cases when hist' is not a legal step
    cases Classical.em (¬ ∃ v', initial' = initial ++ [v'])
    · rename_i h
      apply tsum_congr
      intro z
      split
      · exfalso
        apply h
        exists v0
        rename_i h'
        cases h'
        rfl
      · simp
    rename_i h
    simp at h
    rcases h with ⟨ _, Hv1' ⟩
    simp [Hv1']
    apply tsum_congr
    intro _

    -- Both branches are outside of the cone now
    rw [external_to_cone_zero (by simp_all [cone_of_possibility])]
    rw [external_to_cone_zero (by simp_all [cone_of_possibility])]


lemma cone_constancy [DPSystem ℕ] {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    cone_of_possibility cut initial hist ->
    @constancy_at _ ε₁ ε₂ τ data v0 vk cut initial hist := by
  -- Need theorem to be true for all initial states, since this will increase during the induction
  -- v0 and vk will also change in ways which don't matter
  revert initial v0 vk

  induction cut
  · -- Not true base case (cut 0 is always outside of the cone)
    -- Mercifully it is easy to prove
    intro v0 vk initial Hcone
    unfold constancy_at
    simp [probWhileCut, probWhileFunctional]
    cases (sv1_privMaxC τ data (initial, v0)) <;> simp
    unfold cone_of_possibility at Hcone
    linarith

  rename_i n IH
  intro v0 vk initial Hcone
  -- True base case: are we on the left-hand edge of the cone
  cases Classical.em (hist.length = initial.length)
  · apply cone_left_edge_constancy <;> assumption

  -- If not, unfold the first (and only the first) level of the induction
  unfold constancy_at
  unfold probWhileCut
  unfold probWhileFunctional

  -- If the conditional is false, we are done
  cases (sv1_privMaxC τ data (initial, v0))
  · simp


  -- If the conditional is true, we decrement N by one and add a sample to the history
  rename_i Hcone_interior
  unfold constancy_at at IH
  simp
  apply tsum_congr
  intro ⟨ initial', vk' ⟩

  -- We only need to consider the cases where sv1_privMaxF is nonzero
  -- And this is exactly the case where initial' is initial plus one element
  simp [sv1_privMaxF]
  rw [← ENNReal.tsum_mul_right]
  rw [← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro z
  cases Classical.em (¬ ∃ v', initial' = initial ++ [v'])
  · split
    · exfalso
      rename_i h1 h2
      apply h1
      exists v0
      cases h2
      trivial
    · simp
  rename_i h
  simp at h
  rcases h with ⟨ v', Hinitial' ⟩
  split <;> try simp
  rename_i h
  cases h
  congr 1

  -- Apply the IH
  apply IH

  -- Prove that the new value is in the new cone of possibility
  unfold cone_of_possibility at Hcone
  rcases Hcone with ⟨ Hcone1, Hcone2 ⟩
  unfold cone_of_possibility
  apply And.intro
  · simp
    linarith
  · simp
    apply Nat.lt_iff_add_one_le.mp
    apply LE.le.eq_or_lt at Hcone2
    cases Hcone2
    · exfalso
      apply Hcone_interior
      symm
      trivial
    · trivial


lemma sv2_eq_sv3 [dps : DPSystem ℕ] ε₁ ε₂ l : sv2_privMax ε₁ ε₂ l = sv3_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Step through equal headers
  intro point
  unfold sv2_privMax
  unfold sv3_privMax
  unfold sv3_loop
  simp
  apply tsum_congr
  intro τ
  congr 1
  apply tsum_congr
  intro v0
  congr 1
  apply tsum_congr
  intro final_state
  rcases final_state with ⟨ hist, vk ⟩
  split <;> try rfl
  rename_i H
  simp [H, sv1_threshold]
  clear H

  -- Apply a lemma about eventual constancy
  apply probWhile_apply
  apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ (hist.length + 1)
  intro i H

  -- i is in the cone, reduce by induction
  induction i
  · -- Fake base case
    simp at H
  · rename_i i IH
    -- Real base case
    cases Classical.em (i = hist.length)
    · simp_all

    -- Inductive case: use constancy
    rw [<- IH ?G1]
    case G1 =>
      apply LE.le.ge
      apply GE.ge.le at H
      apply LE.le.lt_or_eq at H
      cases H
      · apply Nat.le_of_lt_succ
        trivial
      · exfalso
        rename_i Hcont _
        apply Hcont
        linarith
    have HK := @cone_constancy dps ε₁ ε₂ τ l v0 vk i [] hist
    unfold constancy_at at HK
    conv =>
      enter [1, 3]
      rw [add_comm]
    apply HK
    unfold cone_of_possibility
    simp
    apply GE.ge.le at H
    apply LE.le.lt_or_eq at H
    cases H
    · linarith
    · exfalso
      rename_i h _
      apply h
      linarith



-- Commute out a single sample from the loop
lemma sv3_loop_unroll_1 [dps : DPSystem ℕ] (τ : ℤ) (ε₁ ε₂ : ℕ+) l point L vk :
    sv3_loop ε₁ ε₂ τ l (point + 1) (L, vk) =
    (do
      let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
      if (sv1_privMaxC τ l (L, vk))
        then (sv3_loop ε₁ ε₂ τ l point (L ++ [vk], vk1))
        else probPure (L, vk)) := by
  conv =>
    lhs
    unfold sv3_loop
    simp [probWhileCut, probWhileFunctional]
  split
  · apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    unfold sv3_loop
    conv =>
      enter [1, 1, a, 1]
      unfold sv1_privMaxF
      simp
    conv =>
      enter [1, 1, a]
      rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro a
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite ?G1]
    case G1 => apply (L ++ [vk], a)
    split
    · conv =>
        rhs
        rw [<- add_zero (_ * _)]
      congr 1
      simp
      intro i HK1 HK2
      exfalso
      apply HK1
      apply HK2
    · exfalso
      rename_i hk
      apply hk
      rfl
  · simp
    apply SLang.ext
    intro ⟨ HF, vkf ⟩
    simp [probBind]
    split <;> try simp
    unfold privNoiseZero
    exact Eq.symm (PMF.tsum_coe (DPSystem.noise (fun _ => 0) 1 ε₁ (4 * ε₂) []))

/-
## Program version 4
  - Executable
  - Presamples at each point, and then executes a deterministic loop
-/

-- An sv4 state is an sv1 state plus a list of presamples
def sv4_state : Type := sv1_state × List ℤ

def sv4_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang { l : List ℤ // List.length l = n } :=
  match n with
  | Nat.zero => return ⟨ [], by simp ⟩
  | Nat.succ n' => do
    let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let vks  <- @sv4_presample dps ε₁ ε₂ n'
    return ⟨ vks ++ [vk1], by simp ⟩


def sv4_privMaxF (s : sv4_state) : SLang sv4_state :=
  match s.2 with
  | [] => probZero
  | (p :: ps) => return ((s.1.1 ++ [s.1.2], p), ps)

def sv4_privMaxC (τ : ℤ) (l : List ℕ) (st : sv4_state) : Bool := sv1_privMaxC τ l st.1

def sv4_loop [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  let presamples <- @sv4_presample dps ε₁ ε₂ point
  let v <- probWhileCut (sv4_privMaxC τ l) sv4_privMaxF (point + 1) (init, presamples)
  return v.1

lemma sv3_loop_unroll_1_alt [dps : DPSystem ℕ] (τ : ℤ) (ε₁ ε₂ : ℕ+) l point (initial_state : sv1_state) :
    sv3_loop ε₁ ε₂ τ l (point + 1) initial_state =
    (do
      let vk1 <- @privNoiseZero dps ε₁ (4 * ε₂)
      if (sv1_privMaxC τ l initial_state)
        then (sv3_loop ε₁ ε₂ τ l point (initial_state.1 ++ [initial_state.2], vk1))
        else probPure initial_state) := by
  rcases initial_state with ⟨ _ , _ ⟩
  rw [sv3_loop_unroll_1]

def len_list_append_rev {m n : ℕ} (x : { l : List ℤ // l.length = m }) (y: { l : List ℤ // l.length = n }) : { l : List ℤ // l.length = n + m } :=
  ⟨ x.1 ++ y.1 , by simp  [add_comm] ⟩



lemma vector_sum_singleton (f : { l : List ℤ // l.length = 1 } -> ENNReal) (P : (x : ℤ) -> ([x].length = 1)) :
    (∑'(x : { l // l.length =  1 }), f x) = (∑' (x : ℤ), f ⟨ [x], P x⟩) := by
  sorry

def sv4_presample_split [DPSystem ℕ] (ε₁ ε₂ : ℕ+) (point : ℕ) :
    sv4_presample ε₁ ε₂ (point + 1) =
    (do
      let presample_1 <- sv4_presample ε₁ ε₂ 1
      let presample_r <- sv4_presample ε₁ ε₂ point
      return len_list_append_rev presample_1 presample_r) := by
  apply SLang.ext
  intro final_state
  simp [sv4_presample]
  conv =>
    enter [1, 1, a]
    rw [<- ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  rw [vector_sum_singleton _ (by simp)]

  have X (x : ℤ): (@tsum.{0, 0} ENNReal _  ENNReal.instTopologicalSpace Int fun (x_1 : Int) =>
                     @ite.{1} ENNReal (@Eq.{1} Int x_1 x) (Classical.propDecidable (@Eq.{1} Int x_1 x))
                       (@OfNat.ofNat.{0} ENNReal 0 (@Zero.toOfNat0.{0} ENNReal instENNRealZero))
                       (@ite.{1} ENNReal (@Eq.{1} Int x x_1) (Int.instDecidableEq x x_1)
                         (@SLang.privNoiseZero _ ε₁
                           (@HMul.hMul.{0, 0, 0} PNat PNat PNat (@instHMul.{0} PNat instPNatMul)
                             (@OfNat.ofNat.{0} PNat 4 (@instOfNatPNatOfNeZeroNat 4 SLang.sv4_presample.proof_5)) ε₂)
                           x_1)
                         0)) = 0 := by
    simp
    aesop
  conv =>
    enter [2, 1, x, 1]
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite x]
    simp
    enter [2]
    skip
    rw [X]
  clear X
  simp
  conv =>
    enter [2, 1, x]
    rw [<- ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp_all [len_list_append_rev]
  -- Can do this by bijection (not congruence)

  -- By bijection
  -- #check tsum_eq_tsum_of_ne_zero_bij
  -- rw [ENNReal.tsum_eq_add_tsum_ite (Int.ofNat point)]

  sorry


def len_1_list_to_val (x : { l : List ℤ // l.length = 1 }) : ℤ :=
  let ⟨ xl, _ ⟩ := x
  match xl with
  | (v :: _) => v


-- When we do induction on point,
-- We will want to generalize over all init
-- Unfolding this loop just moves the first presample into init
-- Which can apply the IH-- since it's some arbitrary init state and a presamples state generated by one fewer point

def sv3_sv4_loop_eq [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) :
    @sv3_loop dps ε₁ ε₂ τ l point init = @sv4_loop dps ε₁ ε₂ τ l point init := by
  revert init
  induction point
  · -- It's a mess but it works
    intro init
    simp [sv3_loop, sv4_loop, probWhileCut, probWhileFunctional, sv4_presample, sv4_privMaxC]
    split
    · simp [sv4_privMaxF, sv1_privMaxF]
      apply SLang.ext
      intro final_state
      simp
    · apply SLang.ext
      intro final_state
      simp
      split
      · rename_i h
        simp_all
        symm
        rw [condition_to_subset]
        rw [ENNReal.tsum_eq_add_tsum_ite ⟨(init, []), rfl⟩]
        simp_all
        conv =>
          rhs
          rw [<- add_zero 1]
        congr
        simp
        intro a
        rcases a
        simp_all
      · symm
        simp
        intro i H
        rcases i
        intro HK
        rename_i hk2 _ _
        apply hk2
        cases HK
        simp at H
        trivial
  · -- Inductive case
    intro init
    rename_i point IH

    -- Unfold sv3_loop on the left
    rw [sv3_loop_unroll_1_alt]

    -- Apply the IH on the left
    -- Doing it this way because I can't conv under the @ite?
    let ApplyIH :
      (do
        let vk1 ← privNoiseZero ε₁ (4 * ε₂)
        if sv1_privMaxC τ l init = true
          then sv3_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) =
      (do
        let vk1 ← privNoiseZero ε₁ (4 * ε₂)
        if sv1_privMaxC τ l init = true
          then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) := by
      simp
      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro _
      congr
      split
      · rw [IH]
      · rfl
    rw [ApplyIH]
    clear ApplyIH IH

    have ToPresample :
        (do
          let vk1 ← privNoiseZero ε₁ (4 * ε₂)
          if sv1_privMaxC τ l init = true then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) =
        (do
          let vps ← sv4_presample ε₁ ε₂ 1
          let vk1 := len_1_list_to_val vps
          if sv1_privMaxC τ l init = true then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1) else probPure init) := by
      apply SLang.ext
      intro final_state
      simp
      -- There is a bijection here
      rw [vector_sum_singleton _ (by simp)]
      apply tsum_congr
      intro x
      simp [len_1_list_to_val]
      simp [sv4_presample]
      rw [ENNReal.tsum_eq_add_tsum_ite x]
      simp

      have X : ( @tsum.{0, 0} ENNReal _
           ENNReal.instTopologicalSpace Int fun (x_1 : Int) =>
           @ite.{1} ENNReal (@Eq.{1} Int x_1 x) (Classical.propDecidable (@Eq.{1} Int x_1 x))
             (@OfNat.ofNat.{0} ENNReal 0 (@Zero.toOfNat0.{0} ENNReal instENNRealZero))
             (@ite.{1} ENNReal (@Eq.{1} Int x x_1) (Int.instDecidableEq x x_1)
               (@SLang.privNoiseZero dps ε₁
                 (@HMul.hMul.{0, 0, 0} PNat PNat PNat (@instHMul.{0} PNat instPNatMul)
                   (@OfNat.ofNat.{0} PNat 4 (@instOfNatPNatOfNeZeroNat 4 SLang.sv4_presample.proof_5)) ε₂)
                 x_1)
               0)) = (0 : ENNReal) := by
        simp
        aesop
      conv =>
        enter [2, 1, 2]
        rw [X]
      simp
    rw [ToPresample]
    clear ToPresample

    -- Now, just need to prove this unfolding of sv4_loop
    unfold sv4_loop
    conv =>
      enter [2]
      unfold probWhileCut
      unfold probWhileFunctional
      unfold sv4_privMaxC

    split
    · conv =>
        enter [2]
        rw [sv4_presample_split]
      simp

      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro vsample_1
      congr 1
      apply tsum_congr
      intro vsample_rest
      congr 1
      -- Seems that the RHS inner sum is an indicator on final_state, so I should
      -- commute that out front
      conv =>
        enter [2, 1, a]
        rw [<- ENNReal.tsum_mul_left]
      conv =>
        enter [2]
        rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro ⟨ ns_state, ns_presamples ⟩ -- Not sure what the variable ns represents?
      simp
      split <;> try simp
      rename_i HF

      -- Investigate the RHS term for simplifications?
      rcases vsample_1 with ⟨ vs1, Hvs1 ⟩
      rcases vsample_rest with ⟨ vsr, Hvsr ⟩
      cases vs1
      · simp at Hvs1
      rename_i vs1 vs_emp
      conv =>
        enter [2, 1, a, 1]
        unfold sv4_privMaxF
        simp [len_list_append_rev]
      have Hemp : vs_emp = [] := by cases vs_emp <;> simp_all
      simp_all
      congr

    · conv =>
        enter [2]
        rw [sv4_presample_split]
      simp
      apply SLang.ext
      intro final_state
      simp
      apply tsum_congr
      intro v1
      split
      · conv =>
          enter [1]
          rw [<- mul_one (sv4_presample _ _ _ _)]
        congr 1
        symm
        sorry
        -- Sum of PMF is 1
      · simp


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- @sv4_loop dps ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

def sv3_eq_sv4 [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv3_privMax dps ε₁ ε₂ l = @sv4_privMax dps ε₁ ε₂ l := by
    unfold sv3_privMax
    unfold sv4_privMax
    simp
    conv =>
      enter [1, x, 1, y, 2, 1, z]
      rw [sv3_sv4_loop_eq]


/-
## Program version 5
  - Executable
  - Isolates the loop for the next step
-/

def sv5_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  let sk <- probWhileCut (sv4_privMaxC τ l) sv4_privMaxF (point + 1) init
  return (sv1_threshold sk.1)

def sv5_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let presamples <- @sv4_presample dps ε₁ ε₂ point
    @sv5_loop τ l point (([], v0), presamples)
  computation point

def sv4_eq_sv5 [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv4_privMax dps ε₁ ε₂ l = @sv5_privMax dps ε₁ ε₂ l := by
  unfold sv4_privMax
  unfold sv5_privMax
  unfold sv4_loop
  unfold sv5_loop
  simp



/-
## Program version 6
  - Executable
  - Changes the loop from a probWhileCut into a single, deterministic, check
-/

-- When you look at exactly n loops in the future, the check evaluates to true
def sv6_privMax_check (τ : ℤ) (l : List ℕ) (s : sv4_state) (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | Nat.succ n' =>
    match s with
    -- If there is more samples on the tape, call recursively
    | ((past, present), (future_next :: future_rest)) =>
      sv4_privMaxC τ l ((past, present), (future_next :: future_rest)) ∧
      sv6_privMax_check τ l ((past ++ [present], future_next), future_rest) n'
    | (_, []) =>
      -- Out of samples on the tape
      false

-- The state sp is a "past configuration" of sc, ie. one we already checked
def is_past_configuration (sp sc : sv4_state) : Prop :=
  (sp.1.1.length ≤ sc.1.1.length) ∧ sp.1.1 ++ [sp.1.2] ++ sp.2 = sc.1.1 ++ [sc.1.2] ++ sc.2

lemma is_past_configuration_ex1 : is_past_configuration (([], 0), []) (([], 0), []) := by
  simp [is_past_configuration]

lemma is_past_configuration_ex2 : is_past_configuration (([], 0), [1]) (([0], 1), []) := by
  simp [is_past_configuration]

lemma is_past_configuration_ex3 : is_past_configuration (([], 0), [1, 2]) (([0], 1), [2]) := by
  simp [is_past_configuration]


-- All past configurations had their loop check execute to True
def sv6_privMax_hist (τ : ℤ) (l : List ℕ) (s : sv4_state) : Prop :=
  ∀ sp, (is_past_configuration sp s) -> sv4_privMaxC τ l sp = true


-- If all past configurations of sp evaluate to True,
-- and the next one evaluates to true,
-- then all past configurations for the next one evaluate to True
lemma sv6_privMax_hist_step (τ : ℤ) (l : List ℕ) (past fut_rest : List ℤ) (present fut : ℤ) :
    sv6_privMax_hist τ l ((past, present), fut :: fut_rest) ->
    sv4_privMaxC τ l ((past ++ [present], fut), fut_rest) ->
    sv6_privMax_hist τ l ((past ++ [present], fut), fut_rest) := by
  intro H1 H2
  unfold sv6_privMax_hist
  intro s H3
  unfold is_past_configuration at H3
  rcases H3 with ⟨ H3, H4 ⟩
  simp_all

  apply Nat.lt_or_eq_of_le at H3
  cases H3
  · -- The length of s1.1.1 is less than or equal to past
    apply H1
    apply And.intro
    · linarith
    · simp_all
  · rename_i Hs11_len
    -- The length of s.1.1 is equal to past.length + 1
    -- Now we can characterize s
    have Hs11 : List.take (past.length + 1) (s.1.1 ++ s.1.2 :: s.2) =
                List.take (past.length + 1) (past ++ present :: fut :: fut_rest) := by
      rw [H4]
    rw [List.take_left' Hs11_len] at Hs11
    simp [List.take_append] at Hs11
    simp_all
    rcases H4 with ⟨ H5, H6 ⟩
    cases s
    rename_i s1 _
    cases s1
    simp_all


def is_past_configuration_strict (sp sc : sv4_state) : Prop :=
  (sp.1.1.length < sc.1.1.length) ∧ sp.1.1 ++ [sp.1.2] ++ sp.2 = sc.1.1 ++ [sc.1.2] ++ sc.2

-- All strictly past configurations had their loop check execute to True
def sv6_privMax_hist_strict (τ : ℤ) (l : List ℕ) (s : sv4_state) : Prop :=
  ∀ sp, (is_past_configuration_strict sp s) -> sv4_privMaxC τ l sp = true

lemma sv6_privMax_hist_step_strict (τ : ℤ) (l : List ℕ) (past fut_rest : List ℤ) (present fut : ℤ) :
    sv6_privMax_hist_strict τ l ((past, present), fut :: fut_rest) ->
    sv4_privMaxC τ l ((past, present), fut :: fut_rest) ->
    sv6_privMax_hist_strict τ l ((past ++ [present], fut), fut_rest) := by
  intro H1 H2
  unfold sv6_privMax_hist_strict
  intro s H3
  unfold is_past_configuration_strict at H3
  rcases H3 with ⟨ H3, H4 ⟩
  simp_all

  apply Nat.lt_or_eq_of_le at H3
  cases H3
  · -- The length of s1.1.1 is less than or equal to past
    apply H1
    apply And.intro
    · linarith
    · simp_all
  · rename_i Hs11_len
    have Hs11 : List.take (past.length) (s.1.1 ++ s.1.2 :: s.2) =
                List.take (past.length) (past ++ present :: fut :: fut_rest) := by
      rw [H4]
    simp at Hs11_len
    rw [List.take_left] at Hs11
    rw [<- Hs11_len] at Hs11
    rw [List.take_left] at Hs11
    cases s
    rename_i s1 s2
    cases s1
    rename_i s11 s12
    simp_all


@[simp]
def sv6_cond_rec (τ : ℤ) (l : List ℕ) (past : List ℤ) (pres : ℤ) (future : List ℤ) : Bool :=
  match future with
  | [] => False
  | (f :: ff) => (sv4_privMaxC τ l ((past, pres), f :: ff) = true) && (sv6_cond_rec τ l (past ++ [pres]) f ff)

@[simp]
def sv6_cond (τ : ℤ) (l : List ℕ) (init : sv4_state) : Bool :=
  sv6_cond_rec τ l init.1.1 init.1.2 init.2

def sv6_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  if (sv6_cond τ l init)
    then return point
    else probZero

lemma sv6_loop_base (τ : ℤ) (l : List ℕ) (point: ℕ) (past: List ℤ) (pres : ℤ) :
    (sv6_loop τ l 0 ((past, pres), [])) point = 0 := by
  simp [sv6_loop]

-- QUESTION: What do we need for equality in the base case?
lemma sv5_sv6_loop_base_case  (τ : ℤ) (l : List ℕ) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    future = [] ->
    List.length future = eval ->
    List.length (past ++ [pres] ++ future) = point ->
    (sv6_loop τ l point ((past, pres), future)) point = (sv5_loop τ l eval ((past, pres), future)) point := by
  intro Hfuture Heval Hstate
  rw [Hfuture]
  simp_all
  rw [<- Heval]
  simp [sv6_loop]
  unfold sv5_loop
  unfold probWhileCut
  unfold probWhileFunctional
  split
  · simp [probWhileCut]
  · simp
    unfold sv4_state
    unfold sv1_state
    rw [ENNReal.tsum_eq_add_tsum_ite ((past, pres), [])]
    symm
    simp only [add_eq_zero]
    apply And.intro
    · simp [sv1_threshold]
      linarith
    · simp
      aesop


-- QUESTION: What do we need for sv6_loop to be equal to sv6_loop_cond (next)
lemma sv6_loop_ind (τ : ℤ) (l : List ℕ) (point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_privMaxC τ l ((past, pres), f :: ff) = true) ->
      List.length (past ++ [pres] ++ f :: ff) = point ->
      (sv6_loop τ l point ((past, pres), f :: ff)) point = (sv6_loop τ l point ((past ++ [pres], f), ff)) point := by
  intro Hcondition _
  unfold sv6_loop
  suffices (sv6_cond τ l ((past, pres), f :: ff) = sv6_cond τ l ((past ++ [pres], f), ff)) by
    split <;> split <;> try rfl
    all_goals simp_all
  conv =>
    lhs
    unfold sv6_cond
    simp
  simp [Hcondition]


-- QUESTION: What do we need for sv5 to be equal to sv5_loop_cond (next) evaluated at point
lemma sv5_loop_ind (τ : ℤ) (l : List ℕ) (eval point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_privMaxC τ l ((past, pres), f :: ff) = true) ->
      (sv5_loop τ l (eval + 1) ((past, pres), f :: ff)) point = (sv5_loop τ l eval ((past ++ [pres], f), ff)) point := by
  intro Hcondition
  conv =>
    lhs
    unfold sv5_loop
    unfold probWhileCut
    unfold probWhileFunctional
  split
  · simp only [bind, pure, sv4_privMaxF, pure_bind]
    unfold sv5_loop
    rfl
  · exfalso
    trivial


def sv6_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let presamples <- @sv4_presample dps ε₁ ε₂ point
    @sv6_loop τ l point (([], v0), presamples)
  computation point



-- sv6_loop and sv5_loop are equal at point (under some conditions)
def sv5_sv6_loop_eq_point (τ : ℤ) (l : List ℕ) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    List.length (past ++ [pres] ++ future) = point  ->
    List.length future = eval ->
    -- sv6_privMax_hist_strict τ l ((past, pres), future) ->
    @sv5_loop τ l eval ((past, pres), future) point = @sv6_loop τ l point ((past, pres), future) point := by
  revert past pres eval
  induction future
  · intro eval past pres H1 H2
    symm
    apply (sv5_sv6_loop_base_case _ _ _ _ _ _ _ (by rfl) H2 H1)
  · rename_i f ff IH
    intro eval past pres Hstate Heval
    cases eval
    · simp at Heval

    rename_i eval
    cases (Classical.em (sv4_privMaxC τ l ((past, pres), f :: ff) = true))
    · rename_i Hcondition
      rw [sv5_loop_ind _ _ _ _ _ _ _ _ Hcondition]
      rw [sv6_loop_ind _ _ _ _ _ _ _ Hcondition Hstate]
      apply (IH eval (past ++ [pres]) f ?G1 ?G2)
      case G1 => simp_all
      case G2 => simp_all

    rename_i Hcondition
    simp at Hcondition
    simp [sv6_loop, Hcondition]
    unfold sv5_loop
    unfold probWhileCut
    unfold probWhileFunctional
    rw [Hcondition]
    simp
    intro i Hi Hk
    simp_all [sv1_threshold]


def sv5_sv6_eq [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    @sv5_privMax dps ε₁ ε₂ l = @sv6_privMax dps ε₁ ε₂ l := by
  unfold sv5_privMax
  unfold sv6_privMax
  apply SLang.ext
  intro eval_point
  simp
  apply tsum_congr
  intro τ
  congr
  apply funext
  intro v0
  congr
  apply funext
  intro future
  congr
  -- Now to prove Equality at the evaluation point

  have Heval : List.length (future : List ℤ) = eval_point := by
    exact Mathlib.Vector.length_val future

  -- length (past + present + future) = point + 1
  rw [sv5_sv6_loop_eq_point]
  · simp
    sorry
  · sorry




-- What am I defining:
-- When I step sv5 (the probWhileCut), unrolling a loop iterate pops the first value out of
-- future, and pushes it onto the initial condition.
-- This means I want to do induction over future.
-- Therefore, I need to establish what it means for a loop body with some of these pops to have
-- not terminated (??)
-- IE. given a state, I want to be able to express the fact that
--   - Every loop check which moved something to the past must have returned false
--   - We are waiting for n loop checks from the current state to return true
-- For the latter, I define sv6_privMax_check
-- For the former, I define sc6_provMax_hist
-- Should be able to establish these inductively based on hist, assuming the first n-1 loop checks are valid





















/-

-- Evaluate the nth conditional starting at state s
-- Evaluate the loop conditional n steps in the future
-- false if the tape runs out
def sv6_privMax_nth (τ : ℤ) (l : List ℕ) (s : sv4_state) (n : ℕ) : Bool :=
  match n with
  | 0 =>
      -- Terminates on the 0th iteration if initial state causes the checck to fail
      ¬ sv4_privMaxC τ l s
  | Nat.succ n' =>
    match s with
    -- If there is more samples on the tape, call recursively
    | ((past, present), (future_next :: future_rest)) =>
      -- sv4_privMaxC τ l ((past, present), (future_next :: future_rest)) ∧        -- Should not terminate here
      sv6_privMax_nth τ l ((past ++ [present], future_next), future_rest) n'
    | (_, []) =>
      -- Out of samples on the tape
      false



-- TODO Test some values of sv6_priv_nth

lemma sv6_privMax_0th_true (τ : ℤ) (l : List ℕ) (s : sv4_state) :
    (sv4_privMaxC τ l s = false) -> (sv6_privMax_nth τ l s 0 = true) := by
  simp [sv6_privMax_nth]

lemma sv6_privMax_0th_false (τ : ℤ) (l : List ℕ) (s : sv4_state) :
    (sv4_privMaxC τ l s = true) -> (sv6_privMax_nth τ l s 0 = false) := by
  simp [sv6_privMax_nth]

lemma sv6_privMax_1th_empty (τ : ℤ) (l : List ℕ) (s : sv1_state) :
    (sv6_privMax_nth τ l (s, []) 1 = false) := by
  simp [sv6_privMax_nth]

-- Inductive formula for n when the tape is empty (not useful)
lemma sv6_privMax_ind_empty (τ : ℤ) (l : List ℕ) (s : sv1_state) (n : ℕ):
    (sv6_privMax_nth τ l (s, []) (n + 1) = false) := by
  simp [sv6_privMax_nth]

-- Inductive formula for n when the tape is not empty (not useful)
lemma sv6_privMax_ind_nonempty (τ : ℤ) (l : List ℕ) pa pr f fs (n : ℕ):
    sv6_privMax_nth τ l ((pa, pr), f :: fs) (n + 1) =
    sv6_privMax_nth τ l ((pa ++ [pr], f), fs) n := by
  simp [sv6_privMax_nth]

def len_constr (s : sv4_state) (p : ℕ) : Prop := s.1.1.length + s.2.length = p

-- These are not true
-- Could change sv4 definition to be monotone so that it is
--
-- -- After its false once, its false forever
-- lemma sv4_constancy_lo τ l P v P' v' (H : sv1_privMaxC τ l (P, v) = false) :
--     (∃ D, P' ++ [v'] = P ++ [v] ++ D) -> (sv1_privMaxC τ l (P', v') = false) := by
--   intro H1
--   rcases H1 with ⟨ D, HD ⟩
--   simp [sv1_privMaxC, sv1_threshold, sv1_noise, exactDiffSum] at H
--   simp [sv1_privMaxC, sv1_threshold, sv1_noise, exactDiffSum]
--   apply (Int.le_trans H)
--   clear H
--
--   sorry
--
-- -- If its true once, its true at all points before
-- lemma sv4_constancy_hi τ l P v P' v' (H : sv1_privMaxC τ l (P, v) = false) :
--     (∃ D, P' ++ [v'] ++ D = P ++ [v]) -> (sv1_privMaxC τ l (P', v') = false) := by
--   sorry

-- Inductive formula for tail
lemma sv6_privMax_ind (τ : ℤ) (l : List ℕ) pa pr f fs (n : ℕ):
    -- sv4_privMaxC τ l ((pa ++ [pr], f), fs) = true ->
    -- len_constr ((pa, pr), f :: fs) n ->
    sv6_privMax_nth τ l ((pa, pr), f :: fs) n =
    sv6_privMax_nth τ l ((pa ++ [pr], f), fs) n := by
  revert pa pr f
  induction fs
  · intro pa pr f
    sorry
  · sorry


def sv6_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ :=
  if (sv6_privMax_nth τ l init point) ∧ ¬ (sv6_privMax_nth τ l init (point + 1))
    then return point
    else probZero

-- If the sv6 return flag is true (at zero) then... the sv4 loop condition is false (at zero)
lemma sv6_privMax_loop_cond_true_0 (τ : ℤ) (l : List ℕ) (init : sv4_state) :
    (len_constr init 0) ->
    (sv6_privMax_nth τ l init 0 = true ∧ sv6_privMax_nth τ l init 1 = false) →
    (sv4_privMaxC τ l init = false) := by
  intro _
  intro ⟨ H1, _ ⟩ -- We can get nothing out of H2?
  simp [sv6_privMax_nth] at H1
  trivial

-- If the sv6 return flag is true (at 1) then
--  there is at least one element in the future list
--  The sv4_condition after executing one shift is false
lemma sv6_privMax_loop_cond_true_1 (τ : ℤ) (l : List ℕ) (init : sv4_state) :
    (len_constr init 1) ->
    (sv6_privMax_nth τ l init 1 = true ∧ sv6_privMax_nth τ l init 2 = false) →
    ∃ init_past init_pres init_fut1 init_futR,
      (init = ((init_past, init_pres), (init_fut1 :: init_futR)) ∧
       sv4_privMaxC τ l ((init_past ++ [init_pres], init_fut1), init_futR) = false) := by
  intro HL
  rcases init with ⟨ ⟨ init_past, init_present ⟩, init_future ⟩
  simp [len_constr] at HL

  intro ⟨ H1, H2 ⟩

  cases init_past
  · -- init_past is [] so init_future is [x]
    simp at HL
    cases init_future
    · exfalso
      simp at HL
    rename_i future_1 future_rest
    cases future_rest
    · -- Continue...
      clear HL

      -- What can we get out of H2? Nothing
      simp [sv6_privMax_nth] at H2

      -- What can we get out of H1?
      simp [sv6_privMax_nth] at H1
      -- sv4_privMaxC τ l (sv4_privMaxF (init)) is false
      -- ∃ x,  sv4_privMaxC τ l (([init_present], future_1), []) = false
      exists []
      exists init_present
      exists future_1
      exists []
    · exfalso
      simp at HL
  · -- init_past is nonempty so init_future is empty
    rename_i past_1 past_rest
    simp at HL
    -- past_rest is empty
    cases past_rest
    · -- init_future is empty
      cases init_future
      · -- Continue...
        clear HL

        -- What can we get out of H2? Nothing
        simp [sv6_privMax_nth] at H2

        -- What can we get out of H1? Contradiction?
        simp [sv6_privMax_nth] at H1
        -- contradiction?

      · exfalso
        simp at HL
    · exfalso
      simp at HL
      linarith


-- So if we know that init.future is nonempty, we should be able to make a conclusion
-- about sv4_loop_cond using the s6 loop flag.

-- lemma sv6_privMax_loop_cond_true (τ : ℤ) (l : List ℕ) (init : sv4_state) (p : ℕ) :
--     (len_constr init p) ->
--     (sv6_privMax_nth τ l init p = true ∧ sv6_privMax_nth τ l init (p + 1) = false) →
--     False := by
--   sorry








-- What can we get out of the case where the sv6 flag is false?

-- When the sv6 flag is false (at zero) then sv4 loop cond at 1 is true
lemma sv6_privMax_loop_cond_false_0 (τ : ℤ) (l : List ℕ) (init : sv4_state) :
    (len_constr init 0) ->
    ¬ (sv6_privMax_nth τ l init 0 = true ∧ sv6_privMax_nth τ l init 1 = false) →
    sv4_privMaxC τ l init = true := by
  intro HL H
  simp [len_constr] at HL
  rcases HL with ⟨ HL1, HL2 ⟩
  rcases init with ⟨ ⟨ init_past, init_present ⟩, init_future ⟩
  simp_all [HL1, HL2]
  rw [sv6_privMax_1th_empty] at H
  simp at H
  simp [sv6_privMax_nth] at H
  trivial






  -- simp [sv6_privMax_nth] at H2
  -- -- H2 is giving us nothing, this is suspicious


  -- sorry


-- Specify that the total length of past and future samples is equal to point (0)
def sv5_sv6_loop_eq_point_0_len_constr (τ : ℤ) (l : List ℕ) (init : sv4_state) :
    len_constr init 0 ->
    @sv5_loop τ l 0 init 0 = @sv6_loop τ l 0 init 0 := by
  intro HC
  simp [sv6_loop]
  split <;> simp
  · rename_i h
    -- rcases h with ⟨ h1, h2 ⟩
    -- FIXME: See above for general lemmas about the loop conditional and sv4 loop evals
    -- Don't do this manually
    sorry
  · rename_i h
    simp at h
    sorry

-- sv6 and sv5 both do (decreasing) induction over the "future" field--
--   When the condition is true for sv5, it shifts one sample out of future, and decreases the cut by 1
--   sv6_loop does ...?

-- So I want inductive formulas for those, ie,
--    init = (x, y, (a :: as))
--      in terms of
--    init = (x ++ [a], y, a)
--      evaluated at point = length(x) + length(a::as)







-- These functions are not equal. However, they are equal at "point" (+- 1?)
def sv5_sv6_loop_eq_point (τ : ℤ) (l : List ℕ) (point eval_point : ℕ) (init : sv4_state) :
    point ≤ eval_point ->
    len_constr init eval_point ->
    @sv5_loop τ l point init eval_point = @sv6_loop τ l point init eval_point := by

  rcases init with ⟨ ⟨ pa, pr ⟩, fu ⟩
  revert pa pr point
  induction fu
  · intro point pa pr HlenIneq Hlen
    simp [len_constr] at Hlen
    -- simp only [sv6_loop]
    simp only [sv5_loop, probWhileCut, probWhileFunctional]
    simp only [pure, pure_apply, ↓reduceIte]
    simp only [sv1_threshold]
    simp only [sv4_privMaxF]
    split
    · simp
      unfold sv6_loop
      split
      · exfalso
        -- There should be a contradiction in here somewhere
        -- TODO: Probably change the definition of sv6_cond so that its monotone?
        sorry
      · simp
    · unfold sv4_state
      unfold sv1_state
      simp
      rw [ENNReal.tsum_eq_add_tsum_ite ((pa, pr), [])]
      conv =>
        rhs
        rw [<- add_zero (sv6_loop _ _ _ _ _)]
      congr
      · simp
        simp [sv6_loop]
        -- ???

        sorry
      · simp
        intro _ _ _ _ _ _ _ _
        rename_i h a b b_1 a_1 a_2 a_3 a_4 a_5
        subst Hlen a_4 a_5 a_3
        simp_all only [Bool.not_eq_true, not_true_eq_false, imp_false]
  · intro point pa pr HlenIneq Hlen
    rename_i f ff IH
    cases point
    · -- point being zero should be a contradiction?
      simp [sv6_loop]
      simp [sv5_loop]
      -- Not sure. Messed up.
      sorry
    rename_i point
    unfold sv5_loop
    unfold probWhileCut
    unfold probWhileFunctional
    sorry


def sv6_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let presamples <- @sv4_presample dps ε₁ ε₂ point
    @sv6_loop τ l point (([], v0), presamples)
  computation point

-/
