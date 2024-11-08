/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Queries.UnboundedMax.Code

noncomputable section
open Classical

namespace SLang

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

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


lemma exactDiffSum_eventually_constant : ∃ K, ∀ K', K ≤ K' -> exactDiffSum K' l = 0 := by
  cases l
  · simp [exactDiffSum, exactClippedSum]
  · rename_i l0 ll
    let K := (@List.maximum_of_length_pos _ _ (l0 :: ll) (by simp))
    exists K
    intro K' HK'
    simp [exactDiffSum, exactClippedSum]
    rw [min_eq_left_iff.mpr ?G1]
    case G1 =>
      simp
      apply le_trans _ HK'
      apply List.le_maximum_of_length_pos_of_mem
      apply List.mem_cons_self
    rw [min_eq_left_iff.mpr ?G1]
    case G1 =>
      apply (@le_trans _ _ _ (↑K') _ _ (by simp))
      simp
      apply le_trans _ HK'
      apply List.le_maximum_of_length_pos_of_mem
      apply List.mem_cons_self
    conv =>
      enter [1, 1, 2, 1]
      rw [(@List.map_inj_left _ _ _ _ (fun n => ↑n)).mpr
            (by
              intro a Ha
              rw [min_eq_left_iff.mpr _]
              simp
              apply le_trans _ HK'
              apply List.le_maximum_of_length_pos_of_mem
              apply List.mem_cons_of_mem
              apply Ha)]
      rfl
    conv =>
      enter [1, 2, 2, 1]
      rw [(@List.map_inj_left _ _ _ _ (fun n => ↑n)).mpr
            (by
              intro a Ha
              rw [min_eq_left_iff.mpr _]
              apply (@le_trans _ _ _ (↑K') _ _ (by simp))
              simp
              apply le_trans _ HK'
              apply List.le_maximum_of_length_pos_of_mem
              apply List.mem_cons_of_mem
              apply Ha)]
      rfl
    simp

/-
lemma probWhile_unroll (C : T -> Bool) (F : T -> SLang T) (I : T) :
      probWhile C F I  =
      (if (C I) then probPure I else (F I) >>= probWhile C F) := by
    s orry

lemma probWhile_mass_unroll_lb (C : T -> Bool) (F : T -> SLang T) (I : T) :
    ∑'t, (((F I) >>= probWhile C F) t) ≤ ∑'t, probWhile C F I t  := by
  conv =>
    rhs
    enter [1, t]
    rw [probWhile_unroll]
  cases (C I)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · conv =>
      enter [2]
      simp
    -- This now uses the upper boudn proof (which we need SPMF for but that's OK)
    have A : tsum (probPure I) = 1 := by s orry
    s orry


lemma probWhile_mass_unroll_lb_eval {T U : Type} (C : T -> Bool) (F : T -> SLang T) (g : U -> T):
    ∑'t, ∑'(u : U), (((F (g u)) >>= probWhile C F) t) ≤ ∑'t, ∑'(u : U), probWhile C F (g u) t  := by
  conv =>
    lhs
    rw [ENNReal.tsum_comm]
  conv =>
    rhs
    rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum
  intro i
  apply probWhile_mass_unroll_lb

-- Apply this lemma K times to the sv0 loop (sum over v0)
/-
lemma sv0_loop_mass_unroll_lb (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (K : ℕ) :
    ∑'t, ∑'(v0 : ℤ), (probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (K, v0)) t ≤
    ∑'t, ∑'(v0 : ℤ), (probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0)) t := by
  induction K
  · rfl
  · rename_i K' IH
    apply le_trans _ (probWhile_mass_unroll_lb_eval (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (fun v0 => (0, v0)))
    simp [sv0_privMaxF, sv0_threshold]
    -- Not sure
    s orry
-/
-/


-- probWhile sv0_privMaxC (sv0_privMaxF ε₁ ε₂ τ l) (False, (0, v0))


-- Intuition: If there is a lower bound on every loop iterate terminating, then the termination probability is 1.

-- Fix l, ε₁, ε₂
-- Can prove that in any state, the loop has probability at least β to terminate
-- How to turn this into a lower bound on the termination probability?


/-
def gen_poisson_trial (C : ℕ -> T → Bool) (F : ℕ × T -> SLang T) (I0 : T) : SLang (Bool × (ℕ × T)) :=
  probWhile
    (fun (x : Bool × (ℕ × T)) => x.1)
    (fun v => do
      let v1 <- F v.2
      return (C v.2.1 v1, (v.2.1 + 1, v1)))
    (True, (0, I0))


lemma gen_poisson_trial_lb (C : ℕ -> T → Bool) (F : ℕ × T -> SLang T) (I : T) (β : NNReal) :
    (∀ x, β ≤ (F x >>= fun v => return C x.1 v) True) ->
    (∀ t, probGeometric (fun b => if b then β else (1 - β)) t.2.1 ≤ gen_poisson_trial C F I t) := by
  intro H
  intro t
  -- rcases t with ⟨ b, ⟨ n, t ⟩ ⟩
  unfold probGeometric
  unfold gen_poisson_trial
  unfold geoLoopCond
  s orry
-/


lemma sv1_ub ε₁ ε₂ l : ∑'s, sv1_privMax ε₁ ε₂ l s ≤ 1 := by
  unfold sv1_privMax

  -- rw [Summable.hasSum_iff ENNReal.summable]


  sorry


/-
History-aware progam computes the same as the history-agnostic program
-/
lemma sv0_eq_sv1 ε₁ ε₂ l : sv0_privMax ε₁ ε₂ l = sv1_privMax ε₁ ε₂ l := by
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
  simp [sv1_threshold]


  sorry





/-
## Program version 2
  - Only moves the loop into a non-executable form, ie. explicitly defines the PMF
-/

def sv2_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
    return (sv1_threshold sk)
  computation point

lemma sv1_sv2_eq ε₁ ε₂ l : sv1_privMax ε₁ ε₂ l = sv2_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro result
  simp [sv1_privMax, sv2_privMax]




/-
## Program version 3
  - Truncates the loop
-/

def sv3_loop (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) (point + 1) init

def sv3_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- sv3_loop ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point


def cone_of_possibility (cut : ℕ) (initial hist : List ℤ) : Prop :=
  (hist.length < cut + initial.length) ∧ (initial.length ≤ hist.length)

def constancy_at {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) : Prop :=
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) (1 + cut) (initial, v0) (hist, vk) =
  probWhileCut (sv1_privMaxC τ data) (sv1_privMaxF ε₁ ε₂) cut       (initial, v0) (hist, vk)


-- All points outside of the cone are zero
lemma external_to_cone_zero :
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
lemma cone_left_edge_constancy {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    hist.length = initial.length ->
    cone_of_possibility cut initial hist ->
    @constancy_at _ _ ε₁ ε₂ τ data v0 vk cut initial hist := by
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


lemma cone_constancy {ε₁ ε₂ : ℕ+} {τ : ℤ} {data : List ℕ} {v0 vk : ℤ} (cut : ℕ) (initial hist : List ℤ) :
    cone_of_possibility cut initial hist ->
    @constancy_at _ _ ε₁ ε₂ τ data v0 vk cut initial hist := by
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


lemma sv2_sv3_eq ε₁ ε₂ l : sv2_privMax ε₁ ε₂ l = sv3_privMax ε₁ ε₂ l := by
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
    have HK := @cone_constancy _ _ ε₁ ε₂ τ l v0 vk i [] hist
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
lemma sv3_loop_unroll_1 (τ : ℤ) (ε₁ ε₂ : ℕ+) l point L vk :
    sv3_loop ε₁ ε₂ τ l (point + 1) (L, vk) =
    (do
      let vk1 <- privNoiseGuess ε₁ ε₂
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
    unfold privNoiseGuess
    unfold privNoiseZero
    symm
    apply PMF.tsum_coe

/-
## Program version 4
  - Executable
  - Presamples at each point, and then executes a deterministic loop
-/

-- An sv4 state is an sv1 state plus a list of presamples
def sv4_state : Type := sv1_state × List ℤ

def sv4_presample (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang { l : List ℤ // List.length l = n } :=
  match n with
  | Nat.zero => return ⟨ [], by simp ⟩
  | Nat.succ n' => do
    let vk1 <- privNoiseGuess ε₁ ε₂
    let vks  <- sv4_presample ε₁ ε₂ n'
    return ⟨ vks ++ [vk1], by simp ⟩


def sv4_privMaxF (s : sv4_state) : SLang sv4_state :=
  match s.2 with
  | [] => probZero
  | (p :: ps) => return ((s.1.1 ++ [s.1.2], p), ps)

def sv4_privMaxC (τ : ℤ) (l : List ℕ) (st : sv4_state) : Bool := sv1_privMaxC τ l st.1

def sv4_loop (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) : SLang sv1_state := do
  let presamples <- sv4_presample ε₁ ε₂ point
  let v <- probWhileCut (sv4_privMaxC τ l) sv4_privMaxF (point + 1) (init, presamples)
  return v.1

lemma sv3_loop_unroll_1_alt (τ : ℤ) (ε₁ ε₂ : ℕ+) l point (initial_state : sv1_state) :
    sv3_loop ε₁ ε₂ τ l (point + 1) initial_state =
    (do
      let vk1 <- privNoiseGuess ε₁ ε₂
      if (sv1_privMaxC τ l initial_state)
        then (sv3_loop ε₁ ε₂ τ l point (initial_state.1 ++ [initial_state.2], vk1))
        else probPure initial_state) := by
  rcases initial_state with ⟨ _ , _ ⟩
  rw [sv3_loop_unroll_1]

def len_list_append_rev {m n : ℕ} (x : { l : List ℤ // l.length = m }) (y: { l : List ℤ // l.length = n }) : { l : List ℤ // l.length = n + m } :=
  ⟨ x.1 ++ y.1 , by simp  [add_comm] ⟩

lemma vector_sum_singleton (f : { l : List ℤ // l.length = 1 } -> ENNReal) (P : (x : ℤ) -> ([x].length = 1)) :
    (∑'(x : { l // l.length =  1 }), f x) = (∑' (x : ℤ), f ⟨ [x], P x⟩) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support, DFunLike.coe]
    exact fun x => ⟨ [x.1], by simp ⟩
  · simp [Function.Injective]
  · simp [Function.support, Set.range]
    intro L HL HN
    cases L
    · simp at HL
    rename_i v R
    cases R
    · exists v
    · simp at HL
  · simp [Function.support, DFunLike.coe]


def vsm_0 (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.headI x.1

def vsm_rest (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.tail x.1, by simp ⟩

def vsm_last (x : {l : List ℤ // l.length = n + 1}) : ℤ :=
  List.getLastI x.1

def vsm_init (x : {l : List ℤ // l.length = n + 1}) : {l : List ℤ // l.length = n } :=
  ⟨ List.dropLast x.1, by simp ⟩


lemma sv4_presample_eval (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n ⟨ List.reverse s, by simp ⟩ = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 s.1 := by
  rcases s with ⟨ s, Hs ⟩
  simp
  revert n
  induction s
  · intro n Hs
    simp_all
    simp at Hs
    unfold sv4_presample
    split
    · simp
    · exfalso
      simp at Hs
  · intro n Hs
    rename_i s0 ss IH
    simp at Hs
    simp only [List.reverse_cons, List.foldl_cons]
    unfold sv4_presample
    cases n
    · exfalso
      simp at Hs
    rename_i n'
    generalize HF : (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) = F
    simp
    conv =>
      enter [1, 1, a]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, i]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (s0, ⟨ ss.reverse, by simp; linarith ⟩)]
    conv =>
      rhs
      rw [<- add_zero (List.foldl _ _ _ )]
      rw [add_comm]
    conv =>
      lhs
      rw [add_comm]
    congr 1
    · simp
      intro _ _ _ _ E
      exfalso
      simp_all
      apply congrArg List.reverse at E
      simp at E
      cases E
      simp_all
    simp
    rw [IH _ ?G1]
    case G1 => linarith
    rw [HF]
    suffices (F (List.foldl F 1 ss) s0 = List.foldl F (F 1 s0) ss) by
      rw [<- HF] at this
      simp at this
      rw [<- HF]
      rw [<- this]
      rw [mul_comm]
    rw [<- (@List.foldl_eq_of_comm'  _ _ F ?G1 1 s0 ss)]
    case G1 =>
      rw [<- HF]
      intros
      simp_all
      repeat rw [ mul_assoc]
      congr 1
      rw [mul_comm]
    simp

lemma sv4_presample_eval' (ε₁ ε₂ : ℕ+) (n : ℕ) (s : { l : List ℤ // List.length l = n }) :
    sv4_presample ε₁ ε₂ n s = List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂ b)) 1 (List.reverse s) := by
  have X := sv4_presample_eval ε₁ ε₂ n ⟨ List.reverse s, by simp ⟩
  simp only [List.reverse_reverse, Subtype.coe_eta] at X
  trivial



lemma vector_sum_merge n (f : ℤ × { l : List ℤ // l.length = n } -> ENNReal) :
    (∑'p, f p) = ∑'(p : {l : List ℤ // l.length = n + 1}), f (vsm_0 p, vsm_rest p) := by
  apply @tsum_eq_tsum_of_ne_zero_bij
  case i =>
    simp [Function.support, DFunLike.coe]
    exact fun x => (vsm_0 x.1, vsm_rest x.1)
  · simp [Function.Injective]
    simp [vsm_0, vsm_rest]
    intro L1 HL1 HL1f L2 HL2 HL2f Heq1 Heq2
    cases L1
    · simp at HL1
    cases L2
    · simp at HL2
    simp_all
  · simp [Function.support, Set.range]
    intro z L HL HF
    exists (z :: L)
    simp
    exists HL
  · simp [Function.support, DFunLike.coe]



-- Split in the other order, used as a helper function
-- REFACTOR: Get rid of this, use sv4_presample_split''
lemma sv4_presample_split' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point }) :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), by simp ⟩ := by
  rcases p with ⟨ L, HL ⟩
  revert HL
  induction L
  · intro HL
    simp at HL
    simp
    conv =>
      rhs
      unfold sv4_presample
    unfold sv4_presample
    split
    · simp
      rw [ENNReal.tsum_eq_add_tsum_ite z]
      conv =>
        lhs
        rw [<- (add_zero (privNoiseGuess _ _ _))]
      congr 1
      · simp
      · symm
        simp
        aesop
    · exfalso
      simp at HL

  · rename_i L0 LL _
    intro HL
    simp
    conv =>
      rhs
      unfold sv4_presample
    simp
    conv =>
      enter [2, 1, a]
      rw [← ENNReal.tsum_mul_left]
      enter [1, b]
      simp
    rw [← ENNReal.tsum_prod]
    rw [ENNReal.tsum_eq_add_tsum_ite (z, ⟨ L0 :: LL, HL ⟩)]
    conv =>
      lhs
      rw [<- (add_zero (_ * _))]
    congr 1
    · simp
    · symm
      simp
      intro A B C D E
      exfalso
      apply (congrArg List.reverse) at E
      simp at E
      cases E
      apply D
      · symm
        trivial
      rename_i E
      apply (congrArg List.reverse) at E
      simp at E
      symm
      trivial


lemma sv4_presample_split'' (ε₁ ε₂ : ℕ+) (point : ℕ) (z : ℤ) (p : { l : List ℤ // List.length l = point }) HP :
    privNoiseGuess ε₁ ε₂ z * sv4_presample ε₁ ε₂ point p =
    sv4_presample ε₁ ε₂ (point + 1) ⟨ (p.1 ++ [z]), HP ⟩ := by rw [sv4_presample_split']

lemma get_last_lemma (L : List ℤ) H : L.getLastI = L.getLast H := by
  rw [List.getLastI_eq_getLast?]
  rw [List.getLast?_eq_getLast_of_ne_nil H]

lemma drop_init_lemma (L : List ℤ) (H : L ≠ []) : L.dropLast ++ [L.getLastI] = L := by
  rw [get_last_lemma _ H]
  apply List.dropLast_append_getLast H

lemma list_lemma_1 {L : List ℤ} (H : L ≠ []) : List.headI L :: L.tail = L := by
  apply List.cons_head?_tail
  apply Option.mem_def.mpr
  cases L
  · exfalso
    simp at H
  simp

lemma list_lemma_2 {L : List ℤ} (H : L ≠ []) : List.dropLast L ++ [L.getLastI] = L := by
  rw [drop_init_lemma L H]


-- Splits and rearranges the functions
def sv4_presample_split (ε₁ ε₂ : ℕ+) (point : ℕ) :
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

  have X (x : ℤ): (@tsum.{0, 0} ENNReal
    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal
      (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
        (@Semiring.toNonAssocSemiring.{0} ENNReal
          (@OrderedSemiring.toSemiring.{0} ENNReal
            (@OrderedCommSemiring.toOrderedSemiring.{0} ENNReal
              (@CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal
                ENNReal.instCanonicallyOrderedCommSemiring))))))
    ENNReal.instTopologicalSpace Int fun (x_1 : Int) =>
    @ite.{1} ENNReal (@Eq.{1} Int x_1 x) (Classical.propDecidable (@Eq.{1} Int x_1 x))
      (@OfNat.ofNat.{0} ENNReal 0 (@Zero.toOfNat0.{0} ENNReal instENNRealZero))
      (@ite.{1} ENNReal (@Eq.{1} Int x x_1) (Int.instDecidableEq x x_1) (@SLang.privNoiseGuess _ _ ε₁ ε₂ x_1)
        0)) = 0 := by simp; aesop
  conv =>
    enter [2, 1, x, 1]
    simp
    rw [ENNReal.tsum_eq_add_tsum_ite x]
    simp
    enter [2]
    rw [X]
  clear X
  simp
  conv =>
    enter [2, 1, x]
    rw [<- ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod]
  simp_all [len_list_append_rev]

  -- Join the sv4_presamples
  conv =>
    enter [1, 1, p]
    rw [sv4_presample_split']
  conv =>
    enter [2, 1, p]
    rw [sv4_presample_split']
  rw [vector_sum_merge]
  rw [vector_sum_merge]

  -- Both sums are singletons
  simp [vsm_rest, vsm_0]
  symm
  rw [ENNReal.tsum_eq_add_tsum_ite final_state]
  -- rcases final_state with ⟨ f, Hf ⟩
  -- simp
  conv =>
    rhs
    rw [<- (zero_add (tsum _))]
  conv =>
    lhs
    rw [add_comm]
  congr 1
  · simp
    intro A B C D
    exfalso
    rcases final_state with ⟨ f, Hf ⟩
    simp_all
    apply C
    rw [list_lemma_1 ?G1]
    intro K
    simp_all

  rw [ENNReal.tsum_eq_add_tsum_ite ⟨[vsm_last final_state] ++ (vsm_init final_state), by simp ⟩ ]
  conv =>
    lhs
    rw [<- (add_zero (@ite _ _ _ _ _))]
    rw [add_comm]
  conv =>
    rhs
    rw [add_comm]
  congr 1
  · symm
    simp
    intro A B C D
    exfalso
    rcases final_state with ⟨ f, Hf ⟩
    simp_all [vsm_rest, vsm_0, vsm_last, vsm_init]
    apply C
    rw [List.getLastI_eq_getLast?]
    unfold Option.iget
    simp
    rw [list_lemma_1]
    intro K
    simp_all

  -- Apply the closed form to evaluate
  rcases final_state with ⟨ f, Hf ⟩
  simp [vsm_rest, vsm_0, vsm_last, vsm_init]
  rw [sv4_presample_eval']
  rw [sv4_presample_eval']
  simp only []

  have Hfoldl_eq :
      (List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.tail ++ [f.headI]).reverse =
       List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.dropLast ++ [f.getLastI]).reverse):= by
    apply List.Perm.foldl_eq
    · intro A B C
      simp
      rw [mul_assoc]
      rw [mul_assoc]
      congr 1
      rw [mul_comm]
    · conv =>
        lhs
        simp
      have H1 : (f.headI :: f.tail.reverse).Perm (f.headI :: f.tail) := by
        apply List.Perm.cons f.headI
        apply List.reverse_perm
      trans
      · apply H1
      rw [list_lemma_1 ?G2]
      case G2 => intro _ ; simp_all
      rw [list_lemma_2 ?G2]
      case G2 => intro _ ; simp_all
      apply List.Perm.symm
      apply List.reverse_perm
  rw [Hfoldl_eq]
  clear Hfoldl_eq
  generalize HX : List.foldl (fun acc b => acc * (privNoiseGuess ε₁ ε₂) b) 1 (f.dropLast ++ [f.getLastI]).reverse = X
  clear HX

  -- Both of the conditionals are true
  split
  · split
    · rfl
    · exfalso
      rename_i A B
      apply B
      rw [list_lemma_2]
      intro K
      simp [K] at Hf
  · split
    · exfalso
      rename_i A B
      apply A
      rw [list_lemma_1]
      intro K
      simp [K] at Hf
    · rfl



def len_1_list_to_val (x : { l : List ℤ // l.length = 1 }) : ℤ :=
  let ⟨ xl, _ ⟩ := x
  match xl with
  | (v :: _) => v

-- When we do induction on point,
-- We will want to generalize over all init
-- Unfolding this loop just moves the first presample into init
-- Which can apply the IH-- since it's some arbitrary init state and a presamples state generated by one fewer point


lemma presample_norm_lemma  (point : ℕ) (ε₁ ε₂ : ℕ+) :
    ∑' (a : { l // l.length = point }), sv4_presample ε₁ ε₂ point a = 1 := by
  induction point
  · simp [sv4_presample]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨ [], sv4_presample.proof_3 ⟩]
    conv =>
      rhs
      rw [<- add_zero 1]
    congr <;> simp
  · rename_i n IH

    -- sv4_presample_split'
    suffices (∑' (a : ℤ × { l : List ℤ // l.length = n }), privNoiseGuess ε₁ ε₂ a.1 * sv4_presample ε₁ ε₂ n a.2 = 1) by
      conv at this =>
        enter [1, 1, a]
        rw [sv4_presample_split']
      rw [<- this]
      symm
      rw [vector_sum_merge]
      simp only []
      simp [vsm_0, vsm_rest]
      symm
      apply @tsum_eq_tsum_of_ne_zero_bij
      case i =>
        simp [Function.support, DFunLike.coe]
        exact fun x => ⟨ ↑(vsm_rest x.1) ++ [vsm_0 x.1], by simp ⟩
      · simp [Function.Injective]
        simp [vsm_0, vsm_rest]
        intro L1 HL1 HL1f L2 HL2 HL2f
        cases L1
        · simp at HL1
        cases L2
        · simp at HL2
        simp_all
        intro X
        rename_i A B C D
        have X1 : List.reverse (B ++ [A]) = List.reverse (D ++ [C]) := by exact congrArg List.reverse X
        simp at X1
        apply X1
      · simp [Function.support, Set.range]
        intro L1 HL1 Hf1
        exists ((vsm_last ⟨ L1, HL1 ⟩) :: (vsm_init ⟨ L1, HL1 ⟩))
        simp
        apply And.intro
        · simp [vsm_0, vsm_rest, vsm_init, vsm_last]
          intro K
          apply Hf1
          rw [<- K]
          congr
          symm
          apply drop_init_lemma
          intro K
          simp [K] at HL1
        · simp [vsm_0, vsm_rest, vsm_init, vsm_last]
          apply drop_init_lemma
          intro K
          simp [K] at HL1
      · simp [Function.support, DFunLike.coe]
        intros
        congr
    rw [ENNReal.tsum_prod']
    conv =>
      enter [1, 1, a]
      simp
      rw [ENNReal.tsum_mul_left]
      rw [IH]
    simp

    -- Change noise to SPMF
    have S := (privNoiseGuess ε₁ ε₂).2
    apply HasSum.tsum_eq S


def sv3_sv4_loop_eq (ε₁ ε₂ : ℕ+) (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv1_state) :
    sv3_loop ε₁ ε₂ τ l point init = sv4_loop ε₁ ε₂ τ l point init := by
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
      ((do
        let vk1 ← privNoiseGuess ε₁ ε₂
        if sv1_privMaxC τ l init = true
          then sv3_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else (SLang.probPure init) : SLang _) =
      ((do
        let vk1 ← privNoiseGuess ε₁ ε₂
        if sv1_privMaxC τ l init = true
          then sv4_loop ε₁ ε₂ τ l point (init.1 ++ [init.2], vk1)
          else probPure init) : SLang _)) := by
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
          let vk1 ← privNoiseGuess ε₁  ε₂
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
      have X : ( @tsum.{0, 0} ENNReal
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} ENNReal
                  (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                    (@Semiring.toNonAssocSemiring.{0} ENNReal
                      (@OrderedSemiring.toSemiring.{0} ENNReal
                        (@OrderedCommSemiring.toOrderedSemiring.{0} ENNReal
                          (@CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal
                            ENNReal.instCanonicallyOrderedCommSemiring))))))
                ENNReal.instTopologicalSpace Int fun (x_1 : Int) =>
                @ite.{1} ENNReal (@Eq.{1} Int x_1 x) (Classical.propDecidable (@Eq.{1} Int x_1 x))
                  (@OfNat.ofNat.{0} ENNReal 0 (@Zero.toOfNat0.{0} ENNReal instENNRealZero))
                  (@ite.{1} ENNReal (@Eq.{1} Int x x_1) (Int.instDecidableEq x x_1) (@SLang.privNoiseGuess dps dpn ε₁ ε₂ x_1)
                    (@OfNat.ofNat.{0} ENNReal 0
                      (@Zero.toOfNat0.{0} ENNReal
                        (@MulZeroClass.toZero.{0} ENNReal
                          (@NonUnitalNonAssocSemiring.toMulZeroClass.{0} ENNReal
                            (@NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal
                              (@Semiring.toNonAssocSemiring.{0} ENNReal
                                (@OrderedSemiring.toSemiring.{0} ENNReal
                                  (@OrderedCommSemiring.toOrderedSemiring.{0} ENNReal
                                    (@CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal
                                      ENNReal.instCanonicallyOrderedCommSemiring))))))))))) = 0 := by simp; aesop

      conv =>
        enter [2, 1, 2]
        skip
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
        apply presample_norm_lemma
      · simp


def sv4_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let sk <- sv4_loop ε₁ ε₂ τ l point ([], v0)
    return (sv1_threshold sk)
  computation point

def sv3_sv4_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv3_privMax ε₁ ε₂ l = sv4_privMax ε₁ ε₂ l := by
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

def sv5_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let presamples <- sv4_presample ε₁ ε₂ point
    @sv5_loop τ l point (([], v0), presamples)
  computation point

def sv4_sv5_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv4_privMax ε₁ ε₂ l = sv5_privMax ε₁ ε₂ l := by
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

-- -- When you look at exactly n loops in the future, the check evaluates to true
-- def sv6_privMax_check (τ : ℤ) (l : List ℕ) (s : sv4_state) (n : ℕ) : Bool :=
--   match n with
--   | 0 => true
--   | Nat.succ n' =>
--     match s with
--     -- If there is more samples on the tape, call recursively
--     | ((past, present), (future_next :: future_rest)) =>
--       sv4_privMaxC τ l ((past, present), (future_next :: future_rest)) ∧
--       sv6_privMax_check τ l ((past ++ [present], future_next), future_rest) n'
--     | (_, []) =>
--       -- Out of samples on the tape
--       false

-- The state sp is a "past configuration" of sc, ie. one we already checked
def is_past_configuration (sp sc : sv4_state) : Prop :=
  (sp.1.1.length ≤ sc.1.1.length) ∧ sp.1.1 ++ [sp.1.2] ++ sp.2 = sc.1.1 ++ [sc.1.2] ++ sc.2

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
  | [] => ¬ (sv4_privMaxC τ l ((past, pres), []))
  | (f :: ff) => (sv4_privMaxC τ l ((past, pres), f :: ff) = true) && (sv6_cond_rec τ l (past ++ [pres]) f ff)

@[simp]
def sv6_cond (τ : ℤ) (l : List ℕ) (init : sv4_state) : Bool :=
  sv6_cond_rec τ l init.1.1 init.1.2 init.2

def sv6_loop (τ : ℤ) (l : List ℕ) (point : ℕ) (init : sv4_state) : SLang ℕ := do
  if (sv6_cond τ l init)
    then return point
    else probZero

-- QUESTION: What do we need for equality in the base case?
lemma sv5_sv6_loop_base_case  (τ : ℤ) (l : List ℕ) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    future = [] ->
    List.length future = eval ->
    List.length (past ++ [pres] ++ future) = point + 1 ->
    (sv6_loop τ l point ((past, pres), future)) point = (sv5_loop τ l eval ((past, pres), future)) point := by
  intro Hfuture Heval Hstate
  rw [Hfuture]
  simp_all
  rw [<- Heval]
  unfold sv5_loop
  unfold probWhileCut
  unfold probWhileFunctional
  split
  · rename_i h
    simp [probWhileCut, sv6_loop]
    rw [h]
    simp
  · rename_i h
    simp at h
    simp [sv6_loop]
    simp [h]
    unfold sv4_state
    unfold sv1_state
    rw [ENNReal.tsum_eq_add_tsum_ite ((past, pres), [])]
    simp [sv1_threshold]
    simp [Hstate]
    conv =>
      lhs
      rw [<- add_zero 1]
    congr
    symm
    simp
    aesop

-- QUESTION: What do we need for sv6_loop to be equal to sv6_loop_cond (next)
lemma sv6_loop_ind (τ : ℤ) (l : List ℕ) (point : ℕ) (past ff: List ℤ) (pres f: ℤ) :
      (sv4_privMaxC τ l ((past, pres), f :: ff) = true) ->
      List.length (past ++ [pres] ++ f :: ff) = point + 1 ->
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


def sv6_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    let presamples <- sv4_presample ε₁ ε₂ point
    @sv6_loop τ l point (([], v0), presamples)
  computation point



-- sv6_loop and sv5_loop are equal at point (under some conditions)
def sv5_sv6_loop_eq_point (τ : ℤ) (l : List ℕ) (point eval : ℕ) (past future : List ℤ) (pres : ℤ) :
    List.length (past ++ [pres] ++ future) = point + 1 ->
    List.length future = eval ->
    -- sv6_privMax_hist_strict τ l ((past, pres), future) ->
    @sv5_loop τ l eval ((past, pres), future) point = @sv6_loop τ l point ((past, pres), future) point := by
  revert past pres eval
  induction future
  · intro eval past pres H1 H2
    symm
    simp at H1
    apply (sv5_sv6_loop_base_case _ _ _ _ _ _ _ (by rfl) H2 ?G2)
    case G2 =>
      simp
      trivial
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


def sv5_sv6_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv5_privMax ε₁ ε₂ l = sv6_privMax ε₁ ε₂ l := by
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
  rw [sv5_sv6_loop_eq_point]
  · simp
  · exact Mathlib.Vector.length_val future


/-
## Program v8
Not executable
Separates out the zero case
-/

def sv7_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    match point with
    | 0 =>
      if (¬ (sv4_privMaxC τ l (([], v0), [])))
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let presamples <- sv4_presample ε₁ ε₂ point'
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv6_cond τ l (([], v0), presamples ++ [vk]))
        then probPure point
        else probZero
  computation point


def sv6_sv7_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv6_privMax ε₁ ε₂ l = sv7_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv6_privMax
  unfold sv7_privMax
  cases point
  · simp [sv6_loop, sv6_cond]
    apply tsum_congr
    intro τ
    congr 1
    apply tsum_congr
    intro v0
    congr 1
    simp [sv4_presample]
    rw [ENNReal.tsum_eq_add_tsum_ite ⟨[], rfl⟩]
    simp
    conv =>
      rhs
      rw [<- (add_zero (@ite _ _ _ _ _))]
    congr 1
    simp
  · rename_i point'
    simp only []
    apply tsum_congr
    intro τ
    congr 1
    apply tsum_congr
    intro v0
    congr 1
    simp
    conv =>
      enter [2, 1, a]
      rw [<- ENNReal.tsum_mul_left]
    conv =>
      lhs
      unfold sv6_loop
    simp
    rw [ENNReal.tsum_comm]
    rw [← ENNReal.tsum_prod]
    conv =>
      rhs
      enter [1, a]
      rw [<- mul_assoc]
      enter [1]
      rw [mul_comm]
      rw [sv4_presample_split']
    apply @tsum_eq_tsum_of_ne_zero_bij
    case i =>
      exact fun x => ⟨ x.1.2 ++ [x.1.1], by simp ⟩
    · simp [Function.Injective]
      intros
      rename_i H
      apply congrArg List.reverse at H
      simp at H
      apply H
    · simp [Function.support, Set.range]
      intros L HL Hf1 Hf2
      exists (vsm_last ⟨ L, HL ⟩)
      exists (vsm_init ⟨ L, HL ⟩)
      simp
      apply And.intro
      · apply And.intro
        · intro K
          apply Hf1
          rw [<- K]
          congr
          simp [vsm_init, vsm_last]
          symm
          apply drop_init_lemma
          intro K
          simp [K] at HL
        · intro K
          apply Hf2
          rw [<- K]
          split <;> split
          · rfl
          · exfalso
            rename_i h1 h2
            apply h2
            rw [<- h1]
            congr
            simp [vsm_init, vsm_last]
            apply drop_init_lemma
            intro K
            simp [K] at HL
          · exfalso
            rename_i h2 h1
            apply h2
            rw [<- h1]
            congr
            simp [vsm_init, vsm_last]
            symm
            apply drop_init_lemma
            intro K
            simp [K] at HL
          · rfl
      · simp [vsm_init, vsm_last]
        apply drop_init_lemma
        intro K
        simp [K] at HL
    · simp

/-
## Program v8

Not executable
Defines G from the paper
-/



def sv8_sum (l : List ℕ) (past : List ℤ) (pres : ℤ) : ℤ := exactDiffSum (List.length past) l + pres

-- G is the maximum value of sv8_sum over the tape
def sv8_G  (l : List ℕ) (past : List ℤ) (pres : ℤ) (future : List ℤ) : ℤ :=
  match future with
  | []        => sv8_sum l past pres
  | (f :: ff) => max (sv8_sum l past pres) (sv8_G l (past ++ [pres]) f ff)

 def sv8_cond (τ : ℤ) (l : List ℕ) (past : List ℤ) (pres : ℤ) (future : List ℤ) (last : ℤ) : Bool :=
   (sv8_G l past pres future < τ) ∧ (sv8_sum l (past ++ [pres] ++ future) last ≥ τ)

def sv8_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- privNoiseThresh ε₁ ε₂
    let v0 <- privNoiseGuess ε₁ ε₂
    match point with
    | 0 =>
      if (sv8_sum l [] v0 ≥ τ)
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let presamples <- sv4_presample ε₁ ε₂ point'
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv8_cond τ l [] v0 presamples vk)
        then probPure point
        else probZero
  computation point


lemma sv7_sv8_cond_eq (τ : ℤ) (l : List ℕ) (v0 : ℤ) (vs : List ℤ) (vk : ℤ) :
    sv8_cond τ l [] v0 vs vk = sv6_cond τ l (([], v0), vs ++ [vk]) := by
  suffices (∀ init, sv8_cond τ l init v0 vs vk = sv6_cond τ l ((init, v0), vs ++ [vk])) by
    apply this
  revert v0
  unfold sv8_cond
  simp
  induction vs
  · intro v0 init
    simp [sv6_cond_rec, sv4_privMaxC, sv1_privMaxC, sv1_threshold, sv1_noise, List.length]
    simp [sv8_G, sv8_sum]
  · intro vi init
    rename_i vi_1 rest IH
    have IH' := IH vi_1 (init ++ [vi])
    simp at IH'
    clear IH
    conv =>
      rhs
      simp [sv6_cond_rec]
    rw [<- IH']
    clear IH'
    cases (decide (τ ≤ sv8_sum l (init ++ vi :: vi_1 :: rest) vk)) <;> simp
    conv =>
      lhs
      unfold sv8_G
      simp
    cases (decide (sv8_G l (init ++ [vi]) vi_1 rest < τ)) <;> simp
    simp [sv4_privMaxC, sv1_privMaxC, sv8_sum, sv1_threshold, sv1_noise]

def sv7_sv8_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv7_privMax ε₁ ε₂ l = sv8_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv7_privMax
  unfold sv8_privMax
  cases point
  · simp [sv4_privMaxC, sv1_privMaxC, sv8_sum, sv1_threshold, sv1_noise]
  rename_i point'
  simp only []
  repeat (apply tsum_congr; intro _; congr 1)
  simp only [sv7_sv8_cond_eq, sv6_cond]



/-
## Program v9

Not executable
Rewritten so that the randomness we will cancel out is right at the front
-/


def sv9_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    match point with
    | 0 => do
      let τ <- privNoiseThresh ε₁ ε₂
      let v0 <- privNoiseGuess ε₁ ε₂
      if (sv8_sum l [] v0 ≥ τ)
        then probPure point
        else probZero
    | (Nat.succ point') => do
      let v0 <- privNoiseGuess ε₁ ε₂
      let presamples <- sv4_presample ε₁ ε₂ point'
      let τ <- privNoiseThresh ε₁ ε₂
      let vk <- privNoiseGuess ε₁ ε₂
      if (sv8_cond τ l [] v0 presamples vk)
        then probPure point
        else probZero
  computation point

def sv8_sv9_eq (ε₁ ε₂ : ℕ+) (l : List ℕ) :
    sv8_privMax ε₁ ε₂ l = sv9_privMax ε₁ ε₂ l := by
  apply SLang.ext
  intro point
  unfold sv8_privMax
  unfold sv9_privMax
  simp
  split
  · simp
  · simp
    conv =>
      lhs
      conv =>
        enter [1, a]
        rw [<- ENNReal.tsum_mul_left]
        conv =>
          enter [1, b]
          rw [<- mul_assoc]
          conv =>
            enter [1]
            rw [mul_comm]
          rw [mul_assoc]
      rw [ENNReal.tsum_comm]
      conv =>
        enter [1, b]
        rw [ENNReal.tsum_mul_left]

    apply tsum_congr
    intro b
    congr 1

    conv =>
      lhs
      conv =>
        enter [1, a]
        rw [<- ENNReal.tsum_mul_left]
        conv =>
          enter [1, b]
          rw [<- mul_assoc]
          conv =>
            enter [1]
            rw [mul_comm]
          rw [mul_assoc]
      rw [ENNReal.tsum_comm]
      conv =>
        enter [1, b]
        rw [ENNReal.tsum_mul_left]



lemma sv9_lb ε₁ ε₂ l : 1 ≤ ∑'s, sv9_privMax ε₁ ε₂ l s  := by
  sorry




/--
sv9 normalizes because sv1 normalizes
-/
def sv9_privMax_SPMF (ε₁ ε₂ : ℕ+) (l : List ℕ) : SPMF ℕ :=
  ⟨ sv9_privMax ε₁ ε₂ l,
    by
      rw [Summable.hasSum_iff ENNReal.summable]
      apply LE.le.antisymm
      · rw [<- sv8_sv9_eq]
        rw [<- sv7_sv8_eq]
        rw [<- sv6_sv7_eq]
        rw [<- sv5_sv6_eq]
        rw [<- sv4_sv5_eq]
        rw [<- sv3_sv4_eq]
        rw [<- sv2_sv3_eq]
        rw [<- sv1_sv2_eq]
        apply sv1_ub
      · apply sv9_lb ⟩




/-

def sv0_eventually_geo_check (ε₁ ε₂ : ℕ+) (τ : ℤ) : SLang Bool := do
    let v <- privNoiseGuess ε₁ ε₂
    return v > τ


/-
-- The sv0 loop is eventually geometric
lemma sv0_loop_eventually_geometric ε₁ ε₂ τ l :
    ∃ K, ∀ s_eval, ∀ v0,
        probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (K, v0) s_eval =
        probGeometric (sv0_eventually_geo_check ε₁ ε₂ τ) s_eval.1 := by
  rcases (@exactDiffSum_eventually_constant l) with ⟨ K, HK ⟩
  exists K
  intro s_eval
  intro v0
  unfold probGeometric
  unfold geoLoopCond
  unfold geoLoopBody
  unfold sv0_privMaxC
  unfold sv0_privMaxF
  unfold sv0_eventually_geo_check
 -/

  s orry


-- def sv0_privMaxC (τ : ℤ) (l : List ℕ) (s : sv0_state) : Bool :=
--   decide (exactDiffSum (sv0_threshold s) l + (sv0_noise s) < τ)

-- sv0_privMaxC is eventually just a (geometric) check

lemma sv0_norm_loop_le ε₁ ε₂ τ : ∑'v0, ∑'n, probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (n, v0) ≤ 1 := by
   s orry

lemma probWhile_unroll (C : T -> Bool) (F : T -> SLang T) (I : T) :
      probWhile C F I =
      (if (C I) then probPure I else (F I) >>= probWhile C F) := by
    s orry
  -- (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (n + Δ, v0)

lemma sv0_norm_loop_ge ε₁ ε₂ v0 τ : 1 ≤ ∑'vf, ∑'n, probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0) (n, vf) := by
  -- To establish a lower bound, it suffices to shift the starting point
  have Hshift : ∀ Δ v0,
       ∑' (n : ℕ), probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (n, v0) ≤
       ∑' (n : ℕ), probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0) := by
    intro Δ
    induction Δ
    · simp
    · rename_i Δ' IH
      intro v0
      apply le_trans _ (IH _)
      clear IH
      conv =>
        rhs
        enter [1, n]
        rw [probWhile_unroll]
      apply ENNReal.tsum_le_tsum
      intro n
      split
      · s orry
      · s orry


      s orry
  s orry

lemma sv0_norm ε₁ ε₂ l : ∑'(x : ℕ),  sv0_privMax ε₁ ε₂ l x = 1 := by
  -- unfold sv0_privMax
  s orry
-/
