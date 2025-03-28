/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
-/
import SampCert
import SampCert.SLang
import SampCert.Samplers.Gaussian.Properties
import Init.Data.Float

open SLang Std Int Array PMF

structure IntHistogram where
  repr : Array ℕ
  min : ℤ
  size : ℕ
  deriving Repr, DecidableEq

def IntHistogram.index (hist : IntHistogram) (i : ℤ) : ℤ := Id.run do
  if i - hist.min < 0 then
    panic! "IntHistogram.get!: index lower than min"
  i + hist.min

def histToSTring (hist : IntHistogram) : String  := Id.run do
  let mut str := ""
  for i in [:hist.repr.size] do
    str := str ++ s!"({hist.index i},{hist.repr.get! i})  "
  return str

instance : ToString IntHistogram where
  toString := histToSTring



/--
  sample `numSamples` times from `dist` into an array and keep track
  of the minimum and maximum sample value
-/
def sample (dist : PMF ℤ) (numSamples : ℕ) : IO ((Array ℤ) × ℤ × ℤ) := do
  if numSamples < 2 then
    panic! "sample: 2 samples at least required"
  let mut samples : Array ℤ := mkArray numSamples 0
  let s₁ : ℤ ← run <| dist
  samples := samples.set! 0 s₁
  let s₂ : ℤ ← run <| dist
  samples := samples.set! 1 s₂
  let mut min : ℤ := s₁
  let mut max : ℤ := s₂
  if s₂ < s₁ then
    min := s₂
    max := s₁
  for i in [2:numSamples] do
    let s : ℤ ← run <| dist
    samples := samples.set! i s
    if s < min then
      min := s
    else if s > max then
      max := s
  return (samples,min,max)

/--
  compute histogram of `samples`
-/
def histogram (samples : Array ℤ) (min max : ℤ) : IO IntHistogram := do
  if max < min then
    panic! "histogram: max less than min"
  let mut hist : Array ℕ := mkArray (1 + max - min).toNat 0
  for v in samples do
    let idx := v - min
    if idx < 0 then
      panic! "histogram: index less than 0"
    hist := hist.set! idx.toNat (hist.get! idx.toNat + 1)
  return { repr := hist, min := min, size := samples.size }

def estimateMean (hist : IntHistogram) : IO Float := do
  let mut acc : Float := 0
  for i in [:hist.repr.size] do
    acc := acc + Float.ofInt (hist.repr.get! i) * Float.ofInt (hist.index i)
  return acc / (hist.size).toFloat

/--
  Moment estimate, unadjusted
-/
def estimateMoment (hist : IntHistogram) (mean : Float) (moment : ℕ) : IO Float := do
  if moment < 2 then
    panic! "estimateMoment: moment must be at least 2"
  let mut acc : Float := 0
  for i in [:hist.repr.size] do
    for _ in [:hist.repr.get! i] do
      acc := acc + (Float.ofInt (hist.index i) - mean)^moment.toFloat
  return acc / (hist.size).toFloat

def estimateVariance (hist : IntHistogram) (mean : Float) : IO Float := do
  estimateMoment hist mean 2

def estimateSkewness (hist : IntHistogram) (mean : Float) (variance : Float) : IO Float := do
  let μ₃ ← estimateMoment hist mean 3
  return μ₃ / (variance^(1.5))

def estimateKurtosis (hist : IntHistogram) (mean : Float) (variance : Float) : IO Float := do
  let μ₃ ← estimateMoment hist mean 4
  return μ₃ / (variance^2)

/--
  Not ideal to reuse IntHistogram for the CDF
  Warning: unnormalized
-/
def estimateCDF (hist : IntHistogram) : IO IntHistogram := do
  if hist.size = 0 then
    panic! "estimateCDF: empty histogram"
  let mut cdf : Array ℕ := mkArray hist.repr.size 0
  cdf := cdf.set! 0 <| hist.repr.get! 0
  for i in [1:cdf.size] do
    cdf := cdf.set! i <| cdf.get! (i - 1) + hist.repr.get! i
  return { repr := cdf, min := hist.min, size := hist.size }

def evalUnnormalizedGaussianPDF (x : ℤ) (num den : ℕ+) : IO Float := do
  return Float.exp <| (- (Float.ofInt x)^2) / (2 * ((num : ℕ).toFloat^2 / (den : ℕ).toFloat^2))

def sumTo (bound : ℤ) (tob : ℤ) (num den : ℕ+) : IO Float := do
  let mut acc : Float := 0
  let dist := Int.natAbs (tob - bound)
  for x in [:dist + 1] do
    let mass ← evalUnnormalizedGaussianPDF (x + bound) num den
    acc := acc + mass
  return acc

def approxNormalizerGaussianPDF (num den : ℕ+) (bound : ℤ) : IO Float := do
  sumTo (-bound) bound num den

def KolmogorovDistance (hist : IntHistogram) (num den : ℕ+) : IO Float := do
  let mut max : Float := 0
  let bound : ℕ := 50 * num^2 -- We should do better when Init has rationals
  let norm : Float ← approxNormalizerGaussianPDF num den bound
  for i in [:hist.repr.size] do
    let sample := hist.index i
    let refCDFUnnormed ← sumTo (- bound) sample num den
    let refCDF := refCDFUnnormed / norm
    let estCDF : Float := (Float.ofNat (hist.repr.get! i)) / (Float.ofInt hist.size)
    let d := (refCDF - estCDF).abs
    if max < d then
      max := d
  return max

def test (num den : ℕ+) (mix numSamples : ℕ) (threshold : Float) : IO Unit := do
  let (samples, min, max) ← sample (DiscreteGaussianPMF num den mix) numSamples
  let hist ← histogram samples min max
  let mean ← estimateMean hist
  let variance ← estimateVariance hist mean
  let skewness ← estimateSkewness hist mean variance
  let kurtosis ← estimateSkewness hist mean variance
  let cdf ← estimateCDF hist
  let D ← KolmogorovDistance cdf num den

  if mean.abs > threshold then
    panic! s!"mean = {mean}"
  IO.println s!"mean = {mean}"

  let trueVariance := (num : ℕ).toFloat^2 / (den : ℕ).toFloat^2
  if (variance - trueVariance).abs > threshold then
    panic! s!"variance = {variance}, true variance is {trueVariance}"
  IO.println s!"variance = {variance}, true variance is {trueVariance}"

  if skewness.abs > threshold then
    panic! s!"skewness = {skewness}"
  IO.println s!"skewness = {skewness}"

  if kurtosis.abs > threshold then
    panic! s!"kurtosis = {kurtosis}"
  IO.println s!"kurtosis = {kurtosis}"

  if D.abs > threshold then
    panic! s!"Kolmogorov distance = {D}"
  IO.println s!"Kolmogorov distance = {D}"


def query_tests : IO Unit := do
  -- Generate list of 1000 numbers from 0 to 15
  let samples := 10000
  let unif_ub := 10
  let data : List ℕ <- List.mapM (fun _ => run <| (SLang.UniformSample_PMF unif_ub)) (List.replicate samples 0)

  let num : ℕ+ := 9
  let den : ℕ+ := 2
  let num_trials := 5

  IO.println s!"[query] testing pure ({(num : ℕ)} / {(den : ℕ)})-DP queries"
  IO.println s!"data := {samples} uniform samples of [0, {(unif_ub : ℕ)}): {(data.take 20)}..."
  IO.println ""

  for i in [:num_trials] do
    let ct <- run <| @privNoisedCount _ PureDPSystem laplace_pureDPSystem num den data
    IO.println s!"#{i} count: {ct}"
  IO.println ""

  let sum_bound : ℕ+ := 10
  for i in [:num_trials] do
    let bs <- run <| @privNoisedBoundedSum PureDPSystem laplace_pureDPSystem sum_bound num den data
    IO.println s!"#{i} bounded sum (bound = {(sum_bound : ℕ)}): {bs}"
  IO.println ""

  for i in [:num_trials] do
    let bs <- run <| @privNoisedBoundedMean PureDPSystem laplace_pureDPSystem sum_bound num den data
    let float_bs := Float.div (Float.ofInt bs.1) (Float.ofInt bs.2)
    IO.println s!"#{i} bounded mean (bound = {(sum_bound : ℕ)}): {bs} (~{float_bs})"
  IO.println ""

  for i in [:num_trials] do
    let h <- run <| @privNoisedHistogram numBins _ { bin := example_bin } PureDPSystem laplace_pureDPSystem num den data
    let h' : List ℤ := h.count.toList.take 25
    IO.println s!"#{i} histogram : {h'}..."
  IO.println ""

  let thresh := 100
  for i in [:num_trials] do
    let m <- run <| @privMaxBinAboveThreshold numBins _ { bin := example_bin } PureDPSystem laplace_pureDPSystem num den thresh data
    IO.println s!"#{i} max bin above threshold (threshold = {(thresh : ℤ)}): {m}"
  IO.println ""

  let τ := 100
  for i in [:num_trials] do
    let m <- run <| @privMeanHistogram PureDPSystem laplace_pureDPSystem numBins { bin := example_bin } unbin num den τ num den data
    let m_float :=
      match m with
      | none => none
      | some bs => some (Float.div (Float.ofInt bs.1) (Float.ofInt bs.2))
    IO.println s!"#{i} (0.5x-privacy) histogram mean, τ = {τ}: {m} (~{m_float})"
  IO.println ""

def statistical_tests : IO Unit := do
  IO.println s!"[samplers] statistical tests"
  let tests : List (ℕ+ × ℕ+ × ℕ) := [
    -- (1,1,0),
    (1,1,7),
    -- (1,1,10000000),
    -- (1,2,0),
    (1,2,7),
    -- (1,2,10000000),
    -- (2,1,0),
    (2,1,7),
    -- (2,1,10000000),
  ]
  for (num,den,mix) in tests do
    IO.println s!"num = {(num : ℕ)}, den = {(den : ℕ)}, mix = {mix}"
    test num den mix 100000 0.1

def sparseVector_tests : IO Unit := do
  let samples := 10000
  let unif_ub := 100
  let data : List ℕ <- List.mapM (fun _ => run <| (SLang.UniformSample_PMF unif_ub)) (List.replicate samples 0)

  let num : ℕ+ := 1
  let den : ℕ+ := 4
  let num_trials := 5

  IO.println s!"[query] testing sparse vector max, ({(num : ℕ)} / {(den : ℕ)})-DP"
  IO.println s!"data := {samples} uniform samples of [0, {(unif_ub : ℕ)}): {(data.take 20)}..."
  IO.println ""

  -- for i in [:num_trials] do
  --   let ct <- run <| @sv0_privMax_PMF PureDPSystem laplace_pureDPSystem num den data
  --   IO.println s!"#{i} sv0 max: {ct}"
  -- IO.println ""

  for i in [:num_trials] do
    let ct <- run <| privUnboundedMax num den data
    IO.println s!"#{i} sv1 max: {ct}"
  IO.println ""



def main : IO Unit := do
  sparseVector_tests
  query_tests
  statistical_tests
