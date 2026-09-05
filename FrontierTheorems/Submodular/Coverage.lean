import FrontierTheorems.Submodular.Basic
import Mathlib.Data.Finset.Card

/-!
# Weighted maximum coverage

For a finite family of finite sets, the weight of the union is a monotone,
normalized submodular objective when the element weights are nonnegative.
No finiteness assumption on the ambient type of elements is needed.
-/

open scoped BigOperators

namespace FrontierTheorems.Submodular

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The total weight covered by the members of `S`. -/
def weightedCoverage (sets : α → Finset β) (weight : β → ℝ) (S : Finset α) : ℝ :=
  ∑ u ∈ S.biUnion sets, weight u

omit [DecidableEq α] in
@[simp] theorem weightedCoverage_empty (sets : α → Finset β) (weight : β → ℝ) :
    weightedCoverage sets weight ∅ = 0 := by
  simp [weightedCoverage]

omit [DecidableEq α] in
@[simp] theorem weightedCoverage_zero (sets : α → Finset β) (S : Finset α) :
    weightedCoverage sets (fun _ => 0) S = 0 := by
  simp [weightedCoverage]

theorem weightedCoverage_union (sets : α → Finset β) (weight : β → ℝ)
    (A B : Finset α) :
    weightedCoverage sets weight (A ∪ B) =
      ∑ u ∈ A.biUnion sets ∪ B.biUnion sets, weight u := by
  unfold weightedCoverage
  rw [show (A ∪ B).biUnion sets = A.biUnion sets ∪ B.biUnion sets by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨a, ha | ha, hua⟩
      · exact Or.inl ⟨a, ha, hua⟩
      · exact Or.inr ⟨a, ha, hua⟩
    · rintro (⟨a, ha, hua⟩ | ⟨a, ha, hua⟩)
      · exact ⟨a, Or.inl ha, hua⟩
      · exact ⟨a, Or.inr ha, hua⟩]

theorem biUnion_inter_subset (sets : α → Finset β) (A B : Finset α) :
    (A ∩ B).biUnion sets ⊆ A.biUnion sets ∩ B.biUnion sets := by
  intro u hu
  simp only [Finset.mem_biUnion] at hu
  obtain ⟨a, ha, hua⟩ := hu
  have haA : a ∈ A := (Finset.mem_inter.mp ha).1
  have haB : a ∈ B := (Finset.mem_inter.mp ha).2
  simp only [Finset.mem_inter]
  exact ⟨Finset.mem_biUnion.mpr ⟨a, haA, hua⟩,
    Finset.mem_biUnion.mpr ⟨a, haB, hua⟩⟩

omit [DecidableEq α] in
theorem weightedCoverage_mono (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) :
    Monotone (weightedCoverage sets weight) := by
  intro S T hST
  unfold weightedCoverage
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    simp only [Finset.mem_biUnion] at hu ⊢
    obtain ⟨s, hs, hus⟩ := hu
    exact ⟨s, hST hs, hus⟩
  · intro u huT huS
    exact hweight u

theorem weightedCoverage_isSubmodular (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) :
    IsSubmodular (weightedCoverage sets weight) := by
  intro A B
  have hsum :
      (∑ u ∈ (A ∩ B).biUnion sets, weight u) ≤
        ∑ u ∈ A.biUnion sets ∩ B.biUnion sets, weight u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact biUnion_inter_subset sets A B
    · intro u huInter huBiUnionInter
      exact hweight u
  calc
    weightedCoverage sets weight (A ∪ B) +
          weightedCoverage sets weight (A ∩ B) =
        (∑ u ∈ A.biUnion sets ∪ B.biUnion sets, weight u) +
          (∑ u ∈ (A ∩ B).biUnion sets, weight u) := by
            rw [weightedCoverage_union]
            rfl
    _ ≤ (∑ u ∈ A.biUnion sets ∪ B.biUnion sets, weight u) +
          (∑ u ∈ A.biUnion sets ∩ B.biUnion sets, weight u) :=
      add_le_add_right hsum _
    _ = weightedCoverage sets weight A + weightedCoverage sets weight B := by
      unfold weightedCoverage
      exact Finset.sum_union_inter

omit [DecidableEq α] in
theorem weightedCoverage_monotone (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) :
    Monotone (weightedCoverage sets weight) :=
  weightedCoverage_mono sets hweight

omit [DecidableEq α] in
theorem weightedCoverage_nonneg (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) (S : Finset α) :
    0 ≤ weightedCoverage sets weight S := by
  unfold weightedCoverage
  exact Finset.sum_nonneg (fun u hu => hweight u)

theorem weightedCoverage_submodular (sets : α → Finset β) {weight : β → ℝ}
    (hweight : ∀ u, 0 ≤ weight u) :
    IsSubmodular (weightedCoverage sets weight) :=
  weightedCoverage_isSubmodular sets hweight

omit [DecidableEq α] in
theorem weightedCoverage_normalized (sets : α → Finset β) (weight : β → ℝ) :
    weightedCoverage sets weight ∅ = 0 :=
  weightedCoverage_empty sets weight

/-- Unweighted coverage as a real-valued objective. -/
def coverage (sets : α → Finset β) (S : Finset α) : ℝ :=
  (S.biUnion sets).card

omit [DecidableEq α] in
@[simp] theorem coverage_empty (sets : α → Finset β) : coverage sets ∅ = 0 := by
  simp [coverage]

omit [DecidableEq α] in
theorem coverage_eq_weightedCoverage_one (sets : α → Finset β) (S : Finset α) :
    coverage sets S = weightedCoverage sets (fun _ => 1) S := by
  simp [coverage, weightedCoverage]

omit [DecidableEq α] in
theorem coverage_eq_card (sets : α → Finset β) (S : Finset α) :
    coverage sets S = ((S.biUnion sets).card : ℝ) := rfl

omit [DecidableEq α] in
theorem coverage_mono (sets : α → Finset β) :
    Monotone (coverage sets) := by
  rw [show coverage sets = weightedCoverage sets (fun _ => 1) from by
    funext S
    exact coverage_eq_weightedCoverage_one sets S]
  apply weightedCoverage_mono
  intro u
  norm_num

theorem coverage_isSubmodular (sets : α → Finset β) :
    IsSubmodular (coverage sets) := by
  rw [show coverage sets = weightedCoverage sets (fun _ => 1) from by
    funext S
    exact coverage_eq_weightedCoverage_one sets S]
  apply weightedCoverage_isSubmodular
  intro u
  norm_num

omit [DecidableEq α] in
theorem coverage_monotone (sets : α → Finset β) :
    Monotone (coverage sets) :=
  coverage_mono sets

theorem coverage_submodular (sets : α → Finset β) :
    IsSubmodular (coverage sets) :=
  coverage_isSubmodular sets

/-- A weighted sum over selected indices, a basic normalized modular objective. -/
def weightedSum (weight : α → ℝ) (S : Finset α) : ℝ :=
  ∑ a ∈ S, weight a

omit [DecidableEq α] in
@[simp] theorem weightedSum_empty (weight : α → ℝ) : weightedSum weight ∅ = 0 := by
  simp [weightedSum]

omit [DecidableEq α] in
@[simp] theorem weightedSum_zero (S : Finset α) : weightedSum (fun _ => 0) S = 0 := by
  simp [weightedSum]

omit [DecidableEq α] in
theorem weightedSum_mono {weight : α → ℝ} (hweight : ∀ a, 0 ≤ weight a) :
    Monotone (weightedSum weight) := by
  intro S T hST
  unfold weightedSum
  apply Finset.sum_le_sum_of_subset_of_nonneg hST
  intro a haT haS
  exact hweight a

theorem weightedSum_isSubmodular (weight : α → ℝ) :
    IsSubmodular (weightedSum weight) := by
  intro A B
  unfold weightedSum
  rw [Finset.sum_union_inter]

omit [DecidableEq α] in
theorem weightedSum_normalized (weight : α → ℝ) : weightedSum weight ∅ = 0 :=
  weightedSum_empty weight

theorem weightedSum_submodular (weight : α → ℝ) :
    IsSubmodular (weightedSum weight) :=
  weightedSum_isSubmodular weight

end FrontierTheorems.Submodular
