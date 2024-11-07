/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/

import SampCert.DifferentialPrivacy.Abstract
import SampCert.DifferentialPrivacy.Pure.System

namespace SLang

variable (ε₁ ε₂ : ℕ+)

variable [dps : DPSystem ℕ]
variable [dpn : DPNoise dps]

/--
Sensitivity bound for the τ threshold
-/
def sens_cov_τ : ℕ+ := 1

/--
Sensitivity bound for each upper bound attempt
-/
def sens_cov_vk : ℕ+ := 1 + sens_cov_τ


/-
## Executable code for the sparse vector mechanism
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
def privNoiseZero (ε₁ ε₂ : ℕ+) : SPMF ℤ := dpn.noise (fun _ => 0) 1 ε₁ ε₂ []


def privNoiseGuess (ε₁ ε₂ : ℕ+) : SPMF ℤ := privNoiseZero ε₁ (2 * sens_cov_vk * ε₂)

def privNoiseThresh (ε₁ ε₂ : ℕ+) : SPMF ℤ := privNoiseZero ε₁ (2 * sens_cov_τ * ε₂)

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

def sv0_privMaxF (ε₁ ε₂ : ℕ+) (s : sv0_state) : SLang sv0_state := do
  let vn <- privNoiseGuess ε₁ ε₂
  let n := (sv0_threshold s) + 1
  return (n, vn)

def sv0_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseThresh ε₁ ε₂
  let v0 <- privNoiseGuess ε₁ ε₂
  let sk <- probWhile (sv0_privMaxC τ l) (sv0_privMaxF ε₁ ε₂) (0, v0)
  return (sv0_threshold sk)

def sv0_privMax_PMF (ε₁ ε₂ : ℕ+) (l : List ℕ) : SPMF ℕ :=
  ⟨ sv0_privMax ε₁ ε₂ l,
    by
      sorry ⟩

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

def sv1_privMaxF (ε₁ ε₂ : ℕ+) (s : sv1_state) : SLang sv1_state := do
  let vn <- privNoiseGuess ε₁ ε₂
  return (s.1 ++ [s.2], vn)

def sv1_privMax (ε₁ ε₂ : ℕ+) (l : List ℕ) : SLang ℕ := do
  let τ <- privNoiseThresh ε₁ ε₂
  let v0 <- privNoiseGuess ε₁ ε₂
  let sk <- probWhile (sv1_privMaxC τ l) (sv1_privMaxF ε₁ ε₂) ([], v0)
  return (sv1_threshold sk)


def sv1_privMax_PMF (ε₁ ε₂ : ℕ+) (l : List ℕ) : SPMF ℕ :=
  ⟨ sv1_privMax ε₁ ε₂ l,
    by
      -- Difficult
      sorry ⟩

end SLang

/-
lemma tsum_iSup_comm (f : T -> U -> ENNReal) : ∑' (a : T), ⨆ (b : U), f a b = ⨆ (b : U), ∑' (a : T), f a b := by

  sorry

-- A version of probWhile that proves normalization, when its arguments are all normal
def SPMF_while (cond : T → Bool) (body : T → SPMF T) (init : T) : SPMF T :=
  ⟨ probWhile cond (fun x => body x) init,
    by
      apply (Summable.hasSum_iff ENNReal.summable).mpr
      unfold probWhile
      rw [tsum_iSup_comm]
      conv =>
        enter [1, 1, cut]
      -- We can establish the ≤ direction easily
      -- ≥ is not true



      -- apply iSup_eq_of_tendsto
      -- · sorry
      -- sorry

      -- rw [ENNReal.tsum_eq_iSup_sum]
      -- apply eq_iff_le_not_lt.mpr
      -- apply And.intro
      -- · apply iSup_le_iff.mpr
      --   sorry
      -- · simp
      --   apply le_iSup_iff.mpr
      --   intro b H
      --   sorry
      ⟩

lemma SPMF_while_eq (cond : T → Bool) (body : T → SPMF T) (init : T) :
    ((SPMF_while cond body init) : SLang T) = (probWhile cond (fun x => body x) init) := by
  simp [SPMF_while]



-/
