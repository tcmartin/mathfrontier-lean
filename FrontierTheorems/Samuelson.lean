import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Samuelson's inequality

For a finite nonempty real sample, no observation can be farther from the
sample mean than `√((n - 1) * variance)`.  The definitions below use the
ordinary finite sums for the mean and population variance.  The statement
includes the edge case `n = 1`, where both sides of the squared inequality
are zero.
-/

noncomputable section

open scoped BigOperators

namespace FrontierTheorems

namespace Samuelson

def sampleMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, x i) / n

def populationVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  (∑ i, (x i - sampleMean x) ^ 2) / n

lemma sum_deviation_eq_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - sampleMean x) = 0 := by
  simp only [sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma sum_deviation_erase_eq_neg {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ (Finset.univ.erase i), (x j - sampleMean x) = -(x i - sampleMean x) := by
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => x j - sampleMean x) (Finset.mem_univ i)
  rw [sum_deviation_eq_zero hn x] at h
  linarith

/--
The squared Samuelson inequality.  For every observation in a nonempty
sample, its squared deviation from the finite-sum sample mean is at most
`(n - 1)` times the finite-sum population variance.
-/
theorem sq_deviation_le (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    (x i - sampleMean x) ^ 2 ≤ (n - 1 : ℝ) * populationVariance x := by
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ.erase i) (f := fun j : Fin n => x j - sampleMean x)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (n - 1 : ℝ) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [sum_deviation_erase_eq_neg hn x i] at hcs
  rw [hcard] at hcs
  have hsquare := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => (x j - sampleMean x) ^ 2) (Finset.mem_univ i)
  have hmain : (x i - sampleMean x) ^ 2 * (n : ℝ) ≤
      (n - 1 : ℝ) * ∑ j, (x j - sampleMean x) ^ 2 := by
    nlinarith [hcs, hsquare]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (x i - sampleMean x) ^ 2 =
        (x i - sampleMean x) ^ 2 * (n : ℝ) / n := by field_simp
    _ ≤ ((n - 1 : ℝ) * ∑ j, (x j - sampleMean x) ^ 2) / n :=
      (div_le_div_of_nonneg_right hmain hnreal.le)
    _ = (n - 1 : ℝ) * populationVariance x := by
      simp only [populationVariance]
      ring

lemma populationVariance_nonneg {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 ≤ populationVariance x := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  · exact_mod_cast hn.le

/-- The absolute-deviation (square-root) form of Samuelson's inequality. -/
theorem abs_deviation_le_sqrt (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    |x i - sampleMean x| ≤ Real.sqrt ((n - 1 : ℝ) * populationVariance x) := by
  have hsq := sq_deviation_le n hn x i
  have hnonneg : 0 ≤ (n - 1 : ℝ) * populationVariance x :=
    mul_nonneg (by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith) (populationVariance_nonneg hn x)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [sq_abs, Real.sq_sqrt hnonneg] using hsq

end Samuelson

end FrontierTheorems
