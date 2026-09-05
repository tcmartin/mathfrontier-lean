import FrontierTheorems.Submodular.Greedy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Nemhauser–Wolsey–Fisher greedy approximation

The comparator is any set of cardinality at most `k`; in particular it can be
an optimal feasible set. The algorithm is the maximum-marginal construction
from `Greedy.lean`, including its behavior after exhausting the ground set.
-/

open scoped BigOperators

namespace FrontierTheorems.Submodular

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The residual against any feasible comparator is bounded by `k` greedy gains. -/
theorem one_step_gap {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (S T : Finset α) {k : ℕ} (hT : T.card ≤ k) :
    f T - f S ≤ (k : ℝ) * (f (greedyStep f S) - f S) := by
  have hU := hsub.diminishingReturns.union_le_sum_marginal S T
  have hTS : f T ≤ f (S ∪ T) := hmono Finset.subset_union_right
  have hsum : (∑ e ∈ T, marginal f S e) ≤
      (T.card : ℝ) * (f (greedyStep f S) - f S) := by
    calc
      _ ≤ ∑ _e ∈ T, (f (greedyStep f S) - f S) :=
        Finset.sum_le_sum fun e _ => marginal_le_greedyStep_gain hmono S e
      _ = _ := by simp; ring
  have hcard : (T.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hT
  have hmul := mul_le_mul_of_nonneg_right hcard (greedyStep_gain_nonneg hmono S)
  linarith

/-- Geometric decay of the residual, for every number of greedy steps. -/
theorem greedy_residual_le {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (hzero : f ∅ = 0) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) (n : ℕ) :
    f T - f (greedy f n) ≤ (1 - 1 / (k : ℝ)) ^ n * f T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 ≤ 1 - 1 / (k : ℝ) := by
    have := (div_le_one hkR).mpr hk1
    linarith
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hstep := one_step_gap hsub hmono (greedy f n) T hT
    have hgain : (f T - f (greedy f n)) / (k : ℝ) ≤
        f (greedy f (n + 1)) - f (greedy f n) := by
      apply (div_le_iff₀ hkR).mpr
      simpa only [greedy_succ, mul_comm] using hstep
    have hcontract : f T - f (greedy f (n + 1)) ≤
        (1 - 1 / (k : ℝ)) * (f T - f (greedy f n)) := by
      simp only [div_eq_mul_inv] at hgain ⊢
      nlinarith
    calc
      _ ≤ (1 - 1 / (k : ℝ)) * (f T - f (greedy f n)) := hcontract
      _ ≤ (1 - 1 / (k : ℝ)) * ((1 - 1 / (k : ℝ)) ^ n * f T) :=
        mul_le_mul_of_nonneg_left ih hr
      _ = _ := by rw [pow_succ]; ring

/-- The exact finite-budget Nemhauser–Wolsey–Fisher guarantee. -/
theorem greedy_approximation {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (hzero : f ∅ = 0) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - (1 - 1 / (k : ℝ)) ^ k) * f T ≤ f (greedy f k) := by
  have := greedy_residual_le hsub hmono hzero hk T hT k
  nlinarith

/-- The finite-budget residual factor is at most `exp (-1)`. -/
theorem residual_factor_le_exp {k : ℕ} (hk : 0 < k) :
    (1 - 1 / (k : ℝ)) ^ k ≤ Real.exp (-1) := by
  exact Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hk : (1 : ℝ) ≤ k)

/-- The classical `1 - 1/e` approximation, stated using the real exponential. -/
theorem greedy_one_sub_inv_e {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (hzero : f ∅ = 0) {k : ℕ} (hk : 0 < k)
    (T : Finset α) (hT : T.card ≤ k) :
    (1 - Real.exp (-1)) * f T ≤ f (greedy f k) := by
  have hnonneg : 0 ≤ f T := by simpa only [hzero] using hmono (Finset.empty_subset T)
  have hfactor := residual_factor_le_exp hk
  have hbound := greedy_approximation hsub hmono hzero hk T hT
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hfactor)]

omit [DecidableEq α] in
/-- A maximum exists among the feasible subsets of a finite ground set. -/
theorem exists_optimal (f : Finset α → ℝ) (k : ℕ) :
    ∃ T : Finset α, T.card ≤ k ∧ ∀ S : Finset α, S.card ≤ k → f S ≤ f T := by
  let feasible := Finset.univ.powerset.filter (fun S : Finset α => S.card ≤ k)
  have hn : feasible.Nonempty := ⟨∅, by simp [feasible]⟩
  obtain ⟨T, hT, hmax⟩ := feasible.exists_max_image f hn
  refine ⟨T, (Finset.mem_filter.mp hT).2, ?_⟩
  intro S hS
  exact hmax S (by simp [feasible, hS])

/-- Feasibility and approximation relative to an actual optimum in one statement. -/
theorem nemhauser_wolsey_fisher {f : Finset α → ℝ} (hsub : IsSubmodular f)
    (hmono : Monotone f) (hzero : f ∅ = 0) {k : ℕ} (hk : 0 < k) :
    (greedy f k).card ≤ k ∧ ∃ T : Finset α, T.card ≤ k ∧
      (∀ S : Finset α, S.card ≤ k → f S ≤ f T) ∧
      (1 - (1 - 1 / (k : ℝ)) ^ k) * f T ≤ f (greedy f k) ∧
      (1 - Real.exp (-1)) * f T ≤ f (greedy f k) := by
  obtain ⟨T, hT, hmax⟩ := exists_optimal f k
  exact ⟨card_greedy_le f k, T, hT, hmax,
    greedy_approximation hsub hmono hzero hk T hT,
    greedy_one_sub_inv_e hsub hmono hzero hk T hT⟩

end FrontierTheorems.Submodular
