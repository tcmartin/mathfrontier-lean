import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite submodular set functions

The lattice inequality, diminishing returns, and a finite telescoping bound
form the combinatorial foundation for greedy approximation guarantees.
-/

open scoped BigOperators

namespace FrontierTheorems.Submodular

variable {α : Type*} [DecidableEq α]

/-- The usual union/intersection definition; monotonicity is a separate hypothesis. -/
def IsSubmodular (f : Finset α → ℝ) : Prop :=
  ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B

/-- The gain from inserting a single element. Inserting an existing element has zero gain. -/
def marginal (f : Finset α → ℝ) (S : Finset α) (e : α) : ℝ :=
  f (insert e S) - f S

/-- Diminishing returns for an element not already in the larger set. -/
def HasDiminishingReturns (f : Finset α → ℝ) : Prop :=
  ∀ A B, A ⊆ B → ∀ e, e ∉ B → marginal f B e ≤ marginal f A e

@[simp] theorem marginal_of_mem (f : Finset α → ℝ) {S : Finset α} {e : α}
    (he : e ∈ S) : marginal f S e = 0 := by
  simp [marginal, Finset.insert_eq_of_mem he]

theorem marginal_nonneg {f : Finset α → ℝ} (hf : Monotone f)
    (S : Finset α) (e : α) : 0 ≤ marginal f S e := by
  exact sub_nonneg.mpr (hf (Finset.subset_insert e S))

theorem IsSubmodular.diminishingReturns {f : Finset α → ℝ} (hf : IsSubmodular f) :
    HasDiminishingReturns f := by
  intro A B hAB e heB
  have h := hf B (insert e A)
  have hunion : B ∪ insert e A = insert e B := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hx | hxe | hxA)
      · exact Or.inr hx
      · exact Or.inl hxe
      · exact Or.inr (hAB hxA)
    · rintro (hxe | hx)
      · exact Or.inr (Or.inl hxe)
      · exact Or.inl hx
  have hinter : B ∩ insert e A = A := by
    ext x
    constructor
    · rw [Finset.mem_inter, Finset.mem_insert]
      rintro ⟨hxB, hxe | hxA⟩
      · exact False.elim (heB (hxe ▸ hxB))
      · exact hxA
    · intro hxA
      rw [Finset.mem_inter, Finset.mem_insert]
      exact ⟨hAB hxA, Or.inr hxA⟩
  rw [hunion, hinter] at h
  dsimp [marginal]
  linarith

theorem HasDiminishingReturns.union_le_sum_marginal {f : Finset α → ℝ}
    (hf : HasDiminishingReturns f) (S T : Finset α) :
    f (S ∪ T) ≤ f S + ∑ e ∈ T, marginal f S e := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert e T heT ih =>
      by_cases heS : e ∈ S
      · simpa [Finset.union_insert, heS, heT] using ih
      · have heST : e ∉ S ∪ T := by
          simp only [Finset.mem_union, not_or]
          exact ⟨heS, heT⟩
        have hdec := hf S (S ∪ T) (Finset.subset_union_left) e heST
        rw [Finset.sum_insert heT, Finset.union_insert]
        calc
          f (insert e (S ∪ T)) = f (S ∪ T) + marginal f (S ∪ T) e := by
            simp [marginal]
          _ ≤ f (S ∪ T) + marginal f S e := add_le_add_right hdec _
          _ ≤ (f S + ∑ x ∈ T, marginal f S x) + marginal f S e :=
            add_le_add_left ih _
          _ = f S + (marginal f S e + ∑ x ∈ T, marginal f S x) := by ring

theorem HasDiminishingReturns.isSubmodular {f : Finset α → ℝ}
    (hf : HasDiminishingReturns f) : IsSubmodular f := by
  have contract : ∀ (A B U : Finset α), A ⊆ B → Disjoint U B →
      f (B ∪ U) - f B ≤ f (A ∪ U) - f A := by
    intro A B U
    induction U using Finset.induction_on with
    | empty => intro _ _; simp
    | @insert e U heU ih =>
        intro hAB hdis
        have hdisU : Disjoint U B := by
          apply Finset.disjoint_left.2
          intro x hxU hxB
          exact Finset.disjoint_left.1 hdis (Finset.mem_insert_of_mem hxU) hxB
        have heB : e ∉ B := by
          intro he
          exact Finset.disjoint_left.1 hdis (Finset.mem_insert_self e U) he
        have heBU : e ∉ B ∪ U := by simp [heB, heU]
        have hsub : A ∪ U ⊆ B ∪ U :=
          Finset.union_subset_union hAB (by rfl)
        have hdec := hf (A ∪ U) (B ∪ U) hsub e heBU
        have hi := ih hAB hdisU
        have hBunion : B ∪ insert e U = insert e (B ∪ U) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        have hAunion : A ∪ insert e U = insert e (A ∪ U) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        rw [hBunion, hAunion]
        dsimp [marginal] at hdec ⊢
        linarith
  intro A B
  have hdis : Disjoint (A \ B) B := by
    apply Finset.disjoint_left.2
    intro e heAB heB
    exact (Finset.mem_sdiff.mp heAB).2 heB
  have h := contract (A ∩ B) B (A \ B) Finset.inter_subset_right hdis
  have hleft : B ∪ (A \ B) = A ∪ B := by
    ext e
    by_cases heA : e ∈ A <;> by_cases heB : e ∈ B <;> simp [heA, heB]
  have hright : (A ∩ B) ∪ (A \ B) = A := by
    ext e
    by_cases heA : e ∈ A <;> by_cases heB : e ∈ B <;> simp [heA, heB]
  rw [hleft, hright] at h
  linarith

theorem isSubmodular_iff_diminishingReturns {f : Finset α → ℝ} :
    IsSubmodular f ↔ HasDiminishingReturns f := by
  exact ⟨IsSubmodular.diminishingReturns, HasDiminishingReturns.isSubmodular⟩

end FrontierTheorems.Submodular
