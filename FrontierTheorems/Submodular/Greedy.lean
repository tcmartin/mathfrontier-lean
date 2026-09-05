import FrontierTheorems.Submodular.Basic

/-!
# Greedy selection on a finite ground set

At each step select an unchosen element with largest marginal gain. When all
elements have been chosen, leave the set unchanged. This defines the actual
finite algorithm; its approximation analysis is proved in the next module.
-/

noncomputable section

namespace FrontierTheorems.Submodular

variable {α : Type*} [DecidableEq α] [Fintype α]

def greedyStep (f : Finset α → ℝ) (S : Finset α) : Finset α :=
  if h : (Finset.univ \ S).Nonempty then
    insert (Classical.choose ((Finset.univ \ S).exists_max_image (marginal f S) h)) S
  else S

def greedy (f : Finset α → ℝ) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => greedyStep f (greedy f n)

@[simp] theorem greedy_zero (f : Finset α → ℝ) : greedy f 0 = ∅ := rfl

@[simp] theorem greedy_succ (f : Finset α → ℝ) (n : ℕ) :
    greedy f (n + 1) = greedyStep f (greedy f n) := rfl

@[simp] theorem greedyStep_univ (f : Finset α → ℝ) :
    greedyStep f Finset.univ = Finset.univ := by
  simp [greedyStep]

theorem subset_greedyStep (f : Finset α → ℝ) (S : Finset α) : S ⊆ greedyStep f S := by
  unfold greedyStep
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem card_greedyStep_le (f : Finset α → ℝ) (S : Finset α) :
    (greedyStep f S).card ≤ S.card + 1 := by
  unfold greedyStep
  split
  · exact Finset.card_insert_le _ _
  · omega

/-- The chosen set always satisfies the cardinality budget, including an empty ground set. -/
theorem card_greedy_le (f : Finset α → ℝ) (n : ℕ) : (greedy f n).card ≤ n := by
  induction n with
  | zero => simp
  | succ n ih => exact (card_greedyStep_le f _).trans (Nat.add_le_add_right ih 1)

theorem card_greedyStep_eq_min (f : Finset α → ℝ) (S : Finset α) :
    (greedyStep f S).card = min (S.card + 1) (Fintype.card α) := by
  by_cases hS : S = Finset.univ
  · subst S
    simp [greedyStep]
  · have hnon : (Finset.univ \ S).Nonempty :=
      Finset.sdiff_nonempty.mpr (by
        intro hsub
        apply hS
        exact Finset.Subset.antisymm (Finset.subset_univ _) hsub)
    have hchoose : Classical.choose
        ((Finset.univ \ S).exists_max_image (marginal f S) hnon) ∉ S := by
      exact (Finset.mem_sdiff.mp
        (Classical.choose_spec
          ((Finset.univ \ S).exists_max_image (marginal f S) hnon)).1).2
    rw [greedyStep, dif_pos hnon, Finset.card_insert_of_notMem hchoose]
    have hnot : ¬(Finset.univ : Finset α) ⊆ S := by
      intro hsub
      apply hS
      exact Finset.Subset.antisymm (Finset.subset_univ _) hsub
    have hlt : S.card < (Finset.univ : Finset α).card :=
      Finset.card_lt_card ⟨Finset.subset_univ _, hnot⟩
    have hlt' : S.card < Fintype.card α := by simpa using hlt
    rw [Nat.min_eq_left (by omega)]

theorem card_greedy_eq_min (f : Finset α → ℝ) (n : ℕ) :
    (greedy f n).card = min n (Fintype.card α) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [greedy_succ, card_greedyStep_eq_min, ih]
      by_cases h : n < Fintype.card α
      · have hn : n ≤ Fintype.card α := h.le
        have hn' : n + 1 ≤ Fintype.card α := by omega
        simp [Nat.min_eq_left hn, Nat.min_eq_left hn']
      · have hn : Fintype.card α ≤ n := Nat.le_of_not_gt h
        have hn' : Fintype.card α ≤ n + 1 := by omega
        rw [Nat.min_eq_right hn, Nat.min_eq_right hn',
          Nat.min_eq_right (by omega)]

theorem greedy_eq_univ_of_card_le (f : Finset α → ℝ) (n : ℕ)
    (h : Fintype.card α ≤ n) : greedy f n = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [card_greedy_eq_min, Nat.min_eq_right h, Finset.card_univ]

theorem greedyStep_gain_nonneg {f : Finset α → ℝ} (hf : Monotone f) (S : Finset α) :
    0 ≤ f (greedyStep f S) - f S :=
  sub_nonneg.mpr (hf (subset_greedyStep f S))

/-- Every single-element gain is at most the actual greedy step's gain. -/
theorem marginal_le_greedyStep_gain {f : Finset α → ℝ} (hf : Monotone f)
    (S : Finset α) (e : α) : marginal f S e ≤ f (greedyStep f S) - f S := by
  by_cases he : e ∈ S
  · simpa [marginal, Finset.insert_eq_of_mem he] using greedyStep_gain_nonneg hf S
  · have h : (Finset.univ \ S).Nonempty := ⟨e, by simp [he]⟩
    have hbest := Classical.choose_spec ((Finset.univ \ S).exists_max_image (marginal f S) h)
    simpa only [greedyStep, dif_pos h, marginal] using hbest.2 e (by simp [he])

theorem greedy_value_monotone {f : Finset α → ℝ} (hf : Monotone f) :
    Monotone (fun n => f (greedy f n)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact hf (subset_greedyStep f _)

end FrontierTheorems.Submodular
