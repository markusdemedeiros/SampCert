/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert.SLang
import SampCert.Samplers.BernoulliNegativeExponential.Code
import SampCert.Samplers.Laplace.Code

/-!
# ``DiscreteGaussianSample`` Implementation

## Implementation Notes

The following identifiers violate our naming scheme, but are currently necessary for extraction:
  - ``DiscreteGaussianSampleLoop``
  - ``DiscreteGaussianSample``
-/

namespace SLang

/--
Sample a candidate for the Discrete Gaussian with variance ``num/den``.
-/
def DiscreteGaussianSampleLoop (num den t : PNat) (mix : ℕ) : SLang (Int × Bool) := do
  let Y : Int ← DiscreteLaplaceSampleMixed t 1 mix
  let y : Nat := Int.natAbs Y
  let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
  let d : PNat := 2 * num * t^2 * den
  let C ← BernoulliExpNegSample n d
  return (Y,C)

def DiscreteGaussianSampleLoop_IBM (num den t : PNat) : SLang (Int × Bool) := do
  let geom_x := (<- probWhile
                       (fun (sample, _) => sample)
                       (fun (_, count) => do return (<- BernoulliExpNegSample 1 t, count + 1))
                       (true, 0)).2
  let bern_b <- BernoulliExpNegSample 1 2
  if (bern_b ∧ ¬ (geom_x = 0))
    then return (0, false)
    else do
      let lap_y := (1 - 2 * (if bern_b then 1 else 0)) * geom_x
      let d : PNat := 2 * num * t^2 * den
      let n : Nat := (Int.natAbs (Int.sub (lap_y * t * den) num))^2
      let bern_c ← BernoulliExpNegSample n d
      if bern_c
        then return (lap_y, true)
        else return (0, false)


/--
``SLang`` term to sample a value from the Discrete Gaussian with variance ``(num/den)``^2.
-/
def DiscreteGaussianSample (num : PNat) (den : PNat) (mix : ℕ) : SLang ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , by simp only [add_pos_iff, zero_lt_one, or_true] ⟩
  let num := num^2
  let den := den^2
  let r ← probUntil (DiscreteGaussianSampleLoop num den t mix) (λ x : Int × Bool => x.2)
  return r.1

def DiscreteGaussianSample_IBM (num : PNat) (den : PNat) : SLang ℤ := do
  let ti : Nat := num.val / den
  let t : PNat := ⟨ ti + 1 , by simp only [add_pos_iff, zero_lt_one, or_true] ⟩
  let num := num^2
  let den := den^2
  let r ← probUntil (DiscreteGaussianSampleLoop_IBM num den t) (λ x : Int × Bool => x.2)
  return r.1



end SLang
