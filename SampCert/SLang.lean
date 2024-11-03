/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log

/-!
# SLang

This file describes the SLang language.

## Implementation notes

Each ``SLang`` value is a distribution over a type (normalization of these distributions
is proven separately). There are no restrictions on the type; the underlying probability
space should be interpreted as discrete.
-/

open Classical Nat ENNReal PMF

/--
The monad of ``SLang`` values
-/
abbrev SLang.{u} (α : Type u) : Type u := α → ℝ≥0∞

namespace PMF

/--
``SLang`` value from ``PMF``
-/
def toSLang (p : PMF α) : SLang α := p.1

@[simp]
theorem toSLang_apply (p : PMF α) (x : α) : (toSLang p x) = p x := by
  unfold toSLang
  unfold DFunLike.coe
  unfold instFunLike
  simp

instance : Coe (PMF α) (SLang α) where
  coe a := toSLang a

end PMF

namespace SLang

/-!
### Program terms of ``SLang``
-/

variable {T U : Type}

/--
The zero distribution as a ``SLang``.
-/
def probZero : SLang T := λ _ : T => 0

/--
The Dirac distribution as a ``SLang``.
-/
@[extern "prob_Pure"]
def probPure (a : T) : SLang T := fun a' => if a' = a then 1 else 0

/--
Monadic bind for ``SLang`` values.
-/
@[extern "prob_Bind"]
def probBind (p : SLang T) (f : T → SLang U) : SLang U :=
  fun b => ∑' a, p a * f a b

instance : Monad SLang where
  pure a := probPure a
  bind pa pb := pa.probBind pb


/--
Uniform distribution on a byte
-/
@[extern "prob_UniformByte"]
def probUniformByte : SLang UInt8 := (fun _ => 1 / UInt8.size)

/--
Upper i bits from a unifomly sampled byte
-/
def probUniformByteUpperBits (i : ℕ) : SLang ℕ := do
  let w <- probUniformByte
  return w.toNat.shiftRight (8 - i)

/--
Uniform distribution on the set [0, 2^i) ⊆ ℕ
-/
def probUniformP2 (i : ℕ) : SLang ℕ :=
  if (i < 8)
  then probUniformByteUpperBits i
  else do
    let v <- probUniformByte
    let w <- probUniformP2 (i - 8)
    return UInt8.size * w + v.toNat

/--
``SLang`` value for the uniform distribution over ``m`` elements, where
the number``m`` is the largest power of two that is at most ``n``.
-/
def UniformPowerOfTwoSample (n : ℕ+) : SLang ℕ :=
  probUniformP2 (log 2 n)


/--
``SLang`` functional which executes ``body`` only when ``cond`` is ``false``.
-/
def probWhileFunctional (cond : T → Bool) (body : T → SLang T) (wh : T → SLang T) : T → SLang T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

/--
``SLang`` value obtained by unrolling a loop body exactly ``n`` times.
-/
def probWhileCut (cond : T → Bool) (body : T → SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => probZero
  | succ n => probWhileFunctional cond body (probWhileCut cond body n) a


/--
``SLang`` value for an unbounded iteration of a loop.
-/
@[extern "prob_While"]
def probWhile (cond : T → Bool) (body : T → SLang T) (init : T) : SLang T :=
  fun x => ⨆ (i : ℕ), (probWhileCut cond body i init x)

/--
``SLang`` value which rejects samples from ``body`` until they satisfy ``cond``.
-/
--@[extern "prob_Until"]
def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
  let v ← body
  probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v

end SLang

namespace PMF

@[extern "my_run"]
opaque run (c : PMF T) : IO T

end PMF

namespace SLang

/--
ProbUniformByte is a proper distribution
-/
def probUniformByte_normalizes : HasSum probUniformByte 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold SLang.probUniformByte
  rw [division_def]
  rw [ENNReal.tsum_mul_right]
  simp only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_one_iff _).mp
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.tsum_toReal_eq ?G1]
  case G1 => simp
  simp only [ENNReal.one_toReal, tsum_const, nsmul_eq_mul, mul_one]
  rw [@Nat.card_eq_of_equiv_fin UInt8 256 ?G1]
  case G1 =>
    apply Equiv.ofBijective (fun v => v.val)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => {val := v : UInt8})
    simp [Function.RightInverse, Function.LeftInverse]
  simp [ENNReal.toReal_inv]

/--
ProbUniformByte as a PMF
-/
def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

end SLang




namespace SLang

-- Could also do this w/ external function, if Lean doesn't optimize it enough.
partial def exec_loop (cond : T → Bool) (exec_body : T → IO T) (init : T) : IO T := do
  if cond init
    then exec_loop cond exec_body (<- exec_body init)
    else return init

-- Defines the IO action associated to executing a SLang term
inductive exec : {α : Type} -> SLang α -> IO α -> Type 1 where
| exec_pure (u : α) : exec (probPure u) (return u)
| exec_bind : exec p ep -> (∀ b , exec (q b) (eq b)) -> exec (probBind p q) (ep >>= eq)
| exec_byte : exec probUniformByte (run probUniformByte_PMF)
| exec_loop {cond : T -> Bool} : (∀ t : T, exec (body t) (ebody t)) -> exec (probWhile cond body init) (exec_loop cond ebody init)

-- has_cmp respects equality
-- has_cmp doesn't need to add an external definition to the PMF type in mathlib
def has_cmp (s : SLang α) : Type 1 := Σ (go : IO α), SLang.exec s go

-- Make it so that you only open the fd once here (top-level)
def run {s : SLang α} (C : has_cmp s) : IO α := C.1

def has_cmp_pure (u : α) : has_cmp (probPure u) :=
  ⟨ _ , exec.exec_pure u ⟩

def has_cmp_bind (Cp : has_cmp p) (Cq : ∀ b , has_cmp (q b)) : has_cmp (probBind p q) :=
  ⟨ _, exec.exec_bind Cp.2 (fun b => (Cq b).2) ⟩

def has_cmp_byte : has_cmp probUniformByte :=
  ⟨ _, exec.exec_byte ⟩

def has_cmp_loop {cond : T -> Bool} (H : ∀ t : T, has_cmp (body t)) : has_cmp (probWhile cond body init) :=
  ⟨ _, exec.exec_loop (fun t => (H t).2) ⟩

end SLang

namespace PMF

-- def has_cmp (p : PMF α) : Type 1 := SLang.has_cmp p
--
-- -- Extraction for PMF's follows from Lean-level equality
-- -- No need to try and bind external def to MathLib internal code
--
-- def has_cmp_pure (u : α) : has_cmp ((Pure.pure u) : PMF α) := by
--   have H : (DFunLike.coe ((Pure.pure u) : PMF _)) = SLang.probPure u := by trivial
--   rw [PMF.has_cmp, H]
--   exact SLang.has_cmp_pure u
--
-- def has_cmp_bind (p : PMF α) (q : α -> PMF β) (H1 : PMF.has_cmp p) (H2 : ∀ a, PMF.has_cmp (q a)) :
--     PMF.has_cmp ((p >>= q) : PMF β) := by
--   have H : (DFunLike.coe ((p >>= q) : PMF β )) = SLang.probBind p (fun a => q a) := by trivial
--   rw [PMF.has_cmp, H]
--   exact SLang.has_cmp_bind H1 H2
--
-- end PMF
