import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Pearson's skewness–kurtosis inequality for finite distributions

For central moments `m₂`, `m₃`, `m₄`, Pearson's inequality is
`m₃² + m₂³ ≤ m₂ * m₄`. The polynomial form includes zero variance.
The normalized version says kurtosis is at least squared skewness plus one.
-/

noncomputable section
open scoped BigOperators

namespace FrontierTheorems.Pearson

def mean {ι : Type*} [Fintype ι] (p x : ι → ℝ) : ℝ := ∑ i, p i * x i

def centralMoment {ι : Type*} [Fintype ι] (p x : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, p i * (x i - mean p x) ^ k

/-- Pearson's inequality for centered weighted data, with nonnegative weights summing to one. -/
theorem centered {ι : Type*} [Fintype ι] (p y : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (hy : ∑ i, p i * y i = 0) :
    (∑ i, p i * y i ^ 3) ^ 2 + (∑ i, p i * y i ^ 2) ^ 3 ≤
      (∑ i, p i * y i ^ 2) * (∑ i, p i * y i ^ 4) := by
  let m₂ := ∑ i, p i * y i ^ 2
  have hcross : (∑ i, p i * y i * (y i ^ 2 - m₂)) = ∑ i, p i * y i ^ 3 := by
    calc
      _ = (∑ i, p i * y i ^ 3) - (∑ i, p i * y i) * m₂ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hy]; ring
  have hfourth : (∑ i, p i * (y i ^ 2 - m₂) ^ 2) =
      (∑ i, p i * y i ^ 4) - m₂ ^ 2 := by
    calc
      _ = (∑ i, p i * y i ^ 4) - 2 * m₂ * (∑ i, p i * y i ^ 2) +
          (∑ i, p i) * m₂ ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hs]; dsimp [m₂]; ring
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun i => p i * y i * (y i ^ 2 - m₂))
    (f := fun i => p i * y i ^ 2)
    (g := fun i => p i * (y i ^ 2 - m₂) ^ 2)
    (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
    (fun i _ => mul_nonneg (hp i) (sq_nonneg _))
    (fun i _ => by ring)
  rw [hcross, hfourth] at hcs
  dsimp [m₂] at hcs
  nlinarith only [hcs]

/-- Pearson's central-moment inequality for any finite probability distribution. -/
theorem central_moment_inequality {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    centralMoment p x 3 ^ 2 + centralMoment p x 2 ^ 3 ≤
      centralMoment p x 2 * centralMoment p x 4 := by
  apply centered p (fun i => x i - mean p x) hp hs
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul, mean]
  ring

/-- With positive variance, kurtosis is at least squared skewness plus one.
Squared skewness is written `m₃² / m₂³`, avoiding a square-root convention. -/
theorem standardized {ι : Type*} [Fintype ι] (p x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hv : 0 < centralMoment p x 2) :
    centralMoment p x 3 ^ 2 / centralMoment p x 2 ^ 3 + 1 ≤
      centralMoment p x 4 / centralMoment p x 2 ^ 2 := by
  have h := central_moment_inequality p x hp hs
  apply (mul_le_mul_iff_left₀ (pow_pos hv 3)).mp
  field_simp
  nlinarith only [h]

end FrontierTheorems.Pearson
