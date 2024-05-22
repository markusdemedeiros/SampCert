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

Each ``SLang`` value is an unnormalized distribution over a type. There are no restrictions
on the type; the underlying measure space should be interpreted as discrete.

MARKUSDE: Are the SLang values intended to be normalizable? I guess not, right?

-/

open Classical Nat ENNReal PMF

noncomputable section

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
The zero distribution as a ``SLang``
-/
def zero : SLang T := λ _ : T => 0

/--
The Dirac distribution as a ``SLang``
-/
def pure (a : T) : SLang T := fun a' => if a' = a then 1 else 0

/--
Monadic bind for ``SLang`` values
-/
def bind (p : SLang T) (f : T → SLang U) : SLang U :=
  fun b => ∑' a, p a * f a b

instance : Monad SLang where
  pure a := pure a
  bind pa pb := pa.bind pb

/--
``SLang`` value for the uniform distribution over ``m`` elements;
the number``m`` is the largest power of two that is at most ``n``.
-/
def uniformPowerOfTwoSample (n : ℕ+) : SLang ℕ :=
  toSLang (PMF.uniformOfFintype (Fin (2 ^ (log 2 n))))
  --((PMF.uniformOfFintype (Fin (2 ^ (log 2 n)))) : PMF ℕ).1

/--
``SLang`` functional which executes ``body`` only when ``cond`` is ``false``.
-/
def whileFunctional (cond : T → Bool) (body : T → SLang T) (wh : T → SLang T) : T → SLang T :=
  λ a : T =>
  if cond a
    then do
      let v ← body a
      wh v
    else return a

-- MARKUSDE: Rename me
/--
``SLang`` value obtained by unrolling a loop body exactly ``n`` times
-/
def probWhileCut (cond : T → Bool) (body : T → SLang T) (n : Nat) (a : T) : SLang T :=
  match n with
  | Nat.zero => zero
  | succ n => whileFunctional cond body (probWhileCut cond body n) a

-- MARKUSDE: Rename me
/--
``SLang`` value for an unbounded iteration of a loop
-/
def probWhile (cond : T → Bool) (body : T → SLang T) (init : T) : SLang T :=
  fun x => ⨆ (i : ℕ), (probWhileCut cond body i init x)

-- MARKUSDE: Rename me
/--
``SLang`` value which rejects samples from ``body`` until they satisfy ``cond``
-/
def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
  let v ← body
  probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v

-- MARKUSDE: Possibly define a truncated ``until`` operator? Many lemmas stated this way

end SLang

#lint docBlame
