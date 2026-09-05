import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Hammersley–Chapman–Robbins bound for finite statistical models

For probability mass functions `p` and `q` on a finite sample space, with `q`
absolutely continuous with respect to `p`, the squared change in an estimator's expectation is bounded
by its variance under `p` times the Pearson chi-square divergence of `q` from `p`.
The unbiased-estimator corollary is the classical two-point HCR lower bound.
-/

noncomputable section

open scoped BigOperators

namespace FrontierTheorems

namespace HCR

def expectation {ι : Type*} [Fintype ι] (p T : ι → ℝ) : ℝ := ∑ i, p i * T i

def variance {ι : Type*} [Fintype ι] (p T : ι → ℝ) : ℝ :=
  ∑ i, p i * (T i - expectation p T) ^ 2

def chiSquare {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, (q i - p i) ^ 2 / p i

/-- Expectation-shift form, including the case of zero chi-square divergence. -/
theorem expectation_shift_sq_le {ι : Type*} [Fintype ι]
    (p q T : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hac : ∀ i, p i = 0 → q i = 0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    (expectation q T - expectation p T) ^ 2 ≤ variance p T * chiSquare p q := by
  have hcenter : (∑ i, (q i - p i) * (T i - expectation p T)) =
      expectation q T - expectation p T := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hp_sum, hq_sum]
    simp [expectation]
  rw [← hcenter]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (f := fun i => p i * (T i - expectation p T) ^ 2)
    (g := fun i => (q i - p i) ^ 2 / p i)
  · intro i _
    exact mul_nonneg (hp i) (sq_nonneg _)
  · intro i _
    exact div_nonneg (sq_nonneg _) (hp i)
  · intro i _
    by_cases hi : p i = 0
    · simp [hi, hac i hi]
    · field_simp [hi]

/-- The finite Hammersley–Chapman–Robbins lower bound under absolute continuity.
`T` is unbiased at the two parameter values `θ` and `η`. -/
theorem lower_bound {ι : Type*} [Fintype ι]
    (p q T : ι → ℝ) (θ η : ℝ)
    (hp : ∀ i, 0 ≤ p i) (_hq : ∀ i, 0 ≤ q i)
    (hac : ∀ i, p i = 0 → q i = 0)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hθ : expectation p T = θ) (hη : expectation q T = η)
    (hχ : 0 < chiSquare p q) :
    (η - θ) ^ 2 / chiSquare p q ≤ variance p T := by
  apply (div_le_iff₀ hχ).2
  simpa [hθ, hη] using expectation_shift_sq_le p q T hp hac hp_sum hq_sum

end HCR

end FrontierTheorems
