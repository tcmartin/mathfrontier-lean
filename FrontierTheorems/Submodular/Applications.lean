import FrontierTheorems.Submodular.Approximation
import FrontierTheorems.Submodular.Coverage

/-!
# Maximum coverage and boundary cases

Coverage assumptions are discharged from the set-union construction. Users of
these theorems provide only their sets, nonnegative weights, and budget.
-/

namespace FrontierTheorems.Submodular

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]

/-- Greedy weighted maximum coverage has the exact finite-budget guarantee. -/
theorem weighted_maximum_coverage (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - (1 - 1 / (k : ℝ)) ^ k) * weightedCoverage sets weight T ≤
      weightedCoverage sets weight (greedy (weightedCoverage sets weight) k) :=
  greedy_approximation (weightedCoverage_isSubmodular sets hweight)
    (weightedCoverage_mono sets hweight) (weightedCoverage_empty sets weight) hk T hT

/-- The classical constant for weighted maximum coverage. -/
theorem weighted_maximum_coverage_one_sub_inv_e (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - Real.exp (-1)) * weightedCoverage sets weight T ≤
      weightedCoverage sets weight (greedy (weightedCoverage sets weight) k) :=
  greedy_one_sub_inv_e (weightedCoverage_isSubmodular sets hweight)
    (weightedCoverage_mono sets hweight) (weightedCoverage_empty sets weight) hk T hT

/-- Unweighted maximum coverage, expressed directly in union cardinalities. -/
theorem maximum_coverage (sets : α → Finset β) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - (1 - 1 / (k : ℝ)) ^ k) * ((T.biUnion sets).card : ℝ) ≤
      (((greedy (coverage sets) k).biUnion sets).card : ℝ) :=
  greedy_approximation (coverage_isSubmodular sets) (coverage_mono sets)
    (coverage_empty sets) hk T hT

theorem maximum_coverage_one_sub_inv_e (sets : α → Finset β) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - Real.exp (-1)) * ((T.biUnion sets).card : ℝ) ≤
      (((greedy (coverage sets) k).biUnion sets).card : ℝ) :=
  greedy_one_sub_inv_e (coverage_isSubmodular sets) (coverage_mono sets)
    (coverage_empty sets) hk T hT

/-- Zero budget is exact, without any assumptions on the objective. -/
theorem greedy_zero_budget (f : Finset α → ℝ) (T : Finset α) (hT : T.card ≤ 0) :
    f T = f (greedy f 0) := by
  have : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hT)
  simp [this]

/-- A budget of one makes the finite NWF factor exactly one. -/
theorem greedy_one_budget_optimal {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (hzero : f ∅ = 0) (T : Finset α) (hT : T.card ≤ 1) :
    f T ≤ f (greedy f 1) := by
  simpa using greedy_approximation hsub hmono hzero (by omega : 0 < 1) T hT

end FrontierTheorems.Submodular
