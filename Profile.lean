/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import SampCert
import SampCert.SLang
import SampCert.Samplers.Gaussian.Properties

open SLang Std PMF

def Nat.toPosUnsafe (n : ℕ) : ℕ+ :=
  match n with
  | 0 => panic! "Nat.toPos! called with argument 0"
  | Nat.succ n' => ⟨ Nat.succ n' , by simp ⟩

def main (args : List String) : IO Unit := do
  let num : ℕ+ := args[0]!.toNat!.toPosUnsafe
  let den : ℕ+ := args[1]!.toNat!.toPosUnsafe
  let iterates := args[2]!.toNat!
  for _ in [:iterates] do
    let _ <- run <| (DiscreteGaussianPMF num den 1000)
  return ()
