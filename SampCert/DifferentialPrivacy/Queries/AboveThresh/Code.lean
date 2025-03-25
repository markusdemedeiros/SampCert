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
def sens_cov_vk : ℕ+ := sens_cov_τ + 1

/--
Noise the constant 0 value using the abstract noise function.

This looks strange, but will specialize to Lap(ε₁/ε₂, 0) in the pure DP case.
-/
def privNoiseZero (ε₁ ε₂ : ℕ+) : SPMF ℤ := dpn.noise (fun _ => 0) 1 ε₁ ε₂ []

def privNoiseGuess (ε₁ ε₂ : ℕ+) : SPMF ℤ := privNoiseZero ε₁ (2 * sens_cov_vk * ε₂)

def privNoiseThresh (ε₁ ε₂ : ℕ+) : SPMF ℤ := privNoiseZero ε₁ (2 * sens_cov_τ * ε₂)

/-
## Program version 1
  - Executable
  - Tracks history of samples
-/




def sv_query (sv_T : Type) : Type := ℕ -> Query sv_T ℤ

def sv1_state : Type := List ℤ × ℤ

def sv1_threshold (s : sv1_state) : ℕ := List.length s.1

def sv1_noise (s : sv1_state) : ℤ := s.2

def sv1_aboveThreshC (qs : sv_query sv_T) (T : ℤ) (τ : ℤ) (l : List sv_T) (s : sv1_state) : Bool :=
  decide (qs (sv1_threshold s) l + (sv1_noise s) < τ + T)
  -- decide (exactDiffSum (sv1_threshold s) l + (sv1_noise s) < τ)

def sv1_aboveThreshF (ε₁ ε₂ : ℕ+) (s : sv1_state) : SLang sv1_state := do
  let vn <- privNoiseGuess ε₁ ε₂
  return (s.1 ++ [s.2], vn)

def sv1_aboveThresh {sv_T : Type} (qs : sv_query sv_T) (T : ℤ) (ε₁ ε₂ : ℕ+) (l : List sv_T) : SLang ℕ := do
  let τ <- privNoiseThresh ε₁ ε₂
  let v0 <- privNoiseGuess ε₁ ε₂
  let sk <- probWhile (sv1_aboveThreshC qs T τ l) (sv1_aboveThreshF ε₁ ε₂) ([], v0)
  return (sv1_threshold sk)

end SLang
