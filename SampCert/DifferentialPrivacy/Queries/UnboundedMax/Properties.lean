/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/

import SampCert.DifferentialPrivacy.Abstract

noncomputable section
open Classical

namespace SLang

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

  -- LHS: singleton sum
  -- RHS: sum over all lists of length "result"
  -- rw [tsum_ite_eq]
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

def sv3_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
  fun (point : ℕ) =>
  let computation : SLang ℕ := do
    let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
    let v0 <- @privNoiseZero dps ε₁ (4 * ε₂)
    let sk <- probWhileCut (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) (point + 1) ([], v0)
    return (sv1_threshold sk)
  computation point


lemma sv2_eq_sv3 [dps : DPSystem ℕ] ε₁ ε₂ l : sv2_privMax ε₁ ε₂ l = sv3_privMax ε₁ ε₂ l := by
  apply SLang.ext

  -- Step through equal headers
  intro point
  unfold sv2_privMax
  unfold sv3_privMax
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

  -- TODO: Move over the eventual constancy statement, and prove it

  -- This statement is wrong, delete it
  --
  -- -- Want to say that the masses of the final returned _value_ are the same,
  -- -- even though the lengths of the histories may change,
  -- -- because past a certain point, adding to the history does not change the
  -- -- probability of returning a given value.
  -- conv =>
  --   unfold sv1_state
  --   congr
  --   · rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  --   · rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  -- apply tsum_congr
  -- intro point'

  sorry



/-
## Program version 4
  - Presamples each vk
  - Iteratively checks if the loop
  - Still loops through prefixes of the vk's iteratively
-/

-- Presamples the list (v_(n-1), v_(n-2), ..., v0)
def sv4_presample [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (n : ℕ) : SLang (List ℤ) := do
  match n with
  | Nat.zero => return []
  | (Nat.succ n') => do
      let v <- @privNoiseZero dps ε₁ (4 * ε₂)
      let l <- sv4_presample ε₁ ε₂ n'
      return (v :: l)

def sv4_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0) && sv4_evaluate_history vs τ l


def sv4_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ (point + 1)
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv4_evaluate_history history τ l && (! sv1_privMaxC τ l (history, vk)))
       then return point
       else probZero
   computation point

lemma sv3_eq_sv4 [dps : DPSystem ℕ] ε₁ ε₂ l : sv3_privMax ε₁ ε₂ l = sv4_privMax ε₁ ε₂ l := by
  sorry





/-
## Program version 5
  - Presamples each vk
  - Performs a single check, rather than a loop
-/
def sv5_evaluate_history (vks : List ℤ) (τ : ℤ) (l : List ℕ) : Bool :=
  match vks with
  | [] => true
  | (v0 :: vs) => sv1_privMaxC τ l (vs, v0)

def sv5_privMax [dps : DPSystem ℕ] (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ :=
   fun (point : ℕ) =>
   let computation : SLang ℕ := do
     let τ <- @privNoiseZero dps ε₁ (2 * ε₂)
     let history <- sv4_presample ε₁ ε₂ (point + 1)
     let vk <- @privNoiseZero dps ε₁ (4 * ε₂)
     if (sv5_evaluate_history history τ l && (! sv1_privMaxC τ l (history, vk)))
       then return point
       else probZero
   computation point

lemma sv4_eq_sv5 [dps : DPSystem ℕ] ε₁ ε₂ l : sv4_privMax ε₁ ε₂ l = sv5_privMax ε₁ ε₂ l := by
  sorry
