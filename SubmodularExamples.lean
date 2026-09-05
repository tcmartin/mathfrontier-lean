import FrontierTheorems.Submodular.Applications

open FrontierTheorems.Submodular

-- An empty ground set remains empty at every budget.
example (f : Finset (Fin 0) → ℝ) (n : ℕ) : greedy f n = ∅ :=
  Subsingleton.elim _ _

-- Zero budget is exact even for a non-monotone, non-normalized objective.
example (f : Finset (Fin 3) → ℝ) (T : Finset (Fin 3)) (hT : T.card ≤ 0) :
    f T = f (greedy f 0) := greedy_zero_budget f T hT

-- Exhaustion is part of the algorithm definition.
example (f : Finset (Fin 2) → ℝ) : greedyStep f Finset.univ = Finset.univ := by simp

-- The finite-budget factors specialize to the sharp classical constants.
example : (1 - (1 - 1 / (2 : ℝ)) ^ 2) = 3 / 4 := by norm_num
example : (1 - (1 - 1 / (3 : ℝ)) ^ 3) = 19 / 27 := by norm_num

-- Submodularity does not silently include monotonicity or nonnegative weights.
example : IsSubmodular (weightedSum (fun _ : Fin 3 => (-1 : ℝ))) :=
  weightedSum_isSubmodular _

private def sets (i : Fin 3) : Finset ℕ :=
  if i = 0 then {0, 1} else if i = 1 then {2, 3} else {0, 2}

-- Coverage counts an overlapping item once.
example : coverage sets {0, 2} = 3 := by
  unfold coverage
  exact_mod_cast (show (({0, 2} : Finset (Fin 3)).biUnion sets).card = 3 by decide)
example : weightedCoverage sets (fun i : ℕ => (i : ℝ) + 1) {0, 2} = 6 := by
  have hcovered : ({0, 2} : Finset (Fin 3)).biUnion sets = {0, 1, 2} := by decide
  unfold weightedCoverage
  rw [hcovered]
  norm_num

-- The two disjoint candidate sets provide a comparator covering all four items.
-- Regardless of the unspecified maximizing tie, greedy covers at least three.
example : 3 ≤ coverage sets (greedy (coverage sets) 2) := by
  have h := maximum_coverage sets (by omega : 0 < 2) {0, 1} (by decide)
  have hcomp : (({0, 1} : Finset (Fin 3)).biUnion sets).card = 4 := by
    decide
  norm_num only [hcomp, Nat.cast_ofNat] at h
  exact h

-- A one-choice weighted instance is solved optimally.
example (T : Finset (Fin 3)) (hT : T.card ≤ 1) :
    weightedCoverage sets (fun _ : ℕ => 0) T ≤
      weightedCoverage sets (fun _ => 0) (greedy (weightedCoverage sets (fun _ => 0)) 1) := by
  exact greedy_one_budget_optimal (weightedCoverage_isSubmodular sets (by intro u; norm_num))
    (weightedCoverage_mono sets (by intro u; norm_num)) (weightedCoverage_empty _ _) T hT

-- Budgets beyond the ground-set size select the whole ground set.
example (f : Finset (Fin 3) → ℝ) : greedy f 5 = Finset.univ :=
  greedy_eq_univ_of_card_le f 5 (by decide)
