import Mathlib.Data.Finset.Basic

-- TODO: These all seem to be missing in mathlib, maybe contribute them?

namespace Finset

-- TODO: Naming
-- TODO: This seems to be missing in mathlib, maybe contribute it?
theorem subset_of_disjoint_singleton_of_eq_unions
    {α : Type*}
    [DecidableEq α]
    {x : α}
    {s t : Finset α}
    (disjoint_singleton_x_s : Disjoint {x} s)
    (eq_union : {x} ∪ s = {x} ∪ t)
  : s ⊆ t := by
    intro y y_mem_s
    cases Decidable.eq_or_ne x y with
      | inl x_eq_y =>
        have y_not_mem_s : y ∉ s := by
          rw [x_eq_y] at disjoint_singleton_x_s
          exact Finset.disjoint_singleton_left.mp disjoint_singleton_x_s
        contradiction
      | inr x_ne_y =>
        have y_mem_singleton_x_union_s : y ∈ {x} ∪ s := by simp [y_mem_s]
        have y_mem_singleton_x_union_t : y ∈ {x} ∪ t := (Finset.ext_iff.mp eq_union y).mp y_mem_singleton_x_union_s
        simp [Finset.mem_union] at y_mem_singleton_x_union_t
        cases y_mem_singleton_x_union_t with
          | inl y_eq_x => have x_eq_y := y_eq_x.symm; contradiction
          | inr y_mem_t => assumption

-- TODO: Naming
-- TODO: This seems to be missing in mathlib, maybe contribute it?
theorem eq_of_disjoint_singleton_of_disjoint_singleton_of_eq_unions
    {α : Type*}
    [DecidableEq α]
    {x : α}
    {s t : Finset α}
    (disjoint_singleton_x_s : Disjoint {x} s)
    (disjoint_singleton_x_t : Disjoint {x} t)
    (eq_union : {x} ∪ s = {x} ∪ t)
  : s = t := by
    ext y
    constructor
    · apply Finset.mem_of_subset
      exact subset_of_disjoint_singleton_of_eq_unions disjoint_singleton_x_s eq_union
    · apply Finset.mem_of_subset
      exact subset_of_disjoint_singleton_of_eq_unions disjoint_singleton_x_t eq_union.symm

theorem toSet_injective {α : Type*} : Function.Injective (@Finset.toSet α) := by
  intro x y h
  simp [toSet] at h
  exact h

def toSetEmbedding {α : Type*} : Finset α ↪ Set α
  := ⟨toSet, toSet_injective⟩

end Finset
