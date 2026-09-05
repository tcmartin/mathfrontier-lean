import FrontierTheorems

open FrontierTheorems
open scoped BigOperators

-- The population-variance convention gives zero at n = 1, with no division by n - 1.
example (a : ℝ) : Samuelson.populationVariance (fun _ : Fin 1 => a) = 0 := by
  simp [Samuelson.populationVariance, Samuelson.sampleMean]

example (a : ℝ) : |a - Samuelson.sampleMean (fun _ : Fin 1 => a)| ≤
    Real.sqrt ((1 - 1 : ℝ) * Samuelson.populationVariance (fun _ : Fin 1 => a)) := by
  simpa using Samuelson.abs_deviation_le_sqrt 1 (by omega) (fun _ => a) 0

-- Samuelson is sharp: for [2, -1, -1], the selected squared deviation is 4.
example : ((![2, -1, -1] : Fin 3 → ℝ) 0 - Samuelson.sampleMean ![2, -1, -1]) ^ 2 =
    (3 - 1 : ℝ) * Samuelson.populationVariance ![2, -1, -1] := by
  norm_num [Samuelson.sampleMean, Samuelson.populationVariance, Fin.sum_univ_succ]

-- Equal two-point masses attain Pearson's lower bound kurtosis = 1.
example : Pearson.centralMoment (fun _ : Fin 2 => (1 / 2 : ℝ)) ![-1, 1] 4 /
    Pearson.centralMoment (fun _ : Fin 2 => (1 / 2 : ℝ)) ![-1, 1] 2 ^ 2 = 1 := by
  norm_num [Pearson.centralMoment, Pearson.mean, Fin.sum_univ_succ]

-- Zero-weight observations cannot change the moments; zero variance is permitted.
example : Pearson.centralMoment (![1, 0] : Fin 2 → ℝ) ![7, 1000] 2 = 0 := by
  norm_num [Pearson.centralMoment, Pearson.mean, Fin.sum_univ_succ]

-- HCR with a genuine zero-probability outcome; the bound is tight for Bernoulli data.
example : (HCR.expectation (![1 / 4, 3 / 4, 0] : Fin 3 → ℝ) ![0, 1, 100] -
      HCR.expectation ![1 / 2, 1 / 2, 0] ![0, 1, 100]) ^ 2 ≤
    HCR.variance ![1 / 2, 1 / 2, 0] ![0, 1, 100] *
      HCR.chiSquare ![1 / 2, 1 / 2, 0] ![1 / 4, 3 / 4, 0] := by
  apply HCR.expectation_shift_sq_le
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

example : HCR.chiSquare (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ![1 / 2, 1 / 2, 0] = 0 := by
  norm_num [HCR.chiSquare, Fin.sum_univ_succ]

example : (3 / 4 - 1 / 2 : ℝ) ^ 2 /
      HCR.chiSquare (![1 / 2, 1 / 2, 0] : Fin 3 → ℝ) ![1 / 4, 3 / 4, 0] ≤
    HCR.variance ![1 / 2, 1 / 2, 0] ![0, 1, 100] := by
  apply HCR.lower_bound
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]
  · norm_num [HCR.expectation, Fin.sum_univ_succ]
  · norm_num [HCR.expectation, Fin.sum_univ_succ]
  · norm_num [HCR.chiSquare, Fin.sum_univ_succ]
