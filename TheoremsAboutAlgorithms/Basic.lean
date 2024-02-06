import Init.Core -- Iff
import Mathlib.Init.Set -- Set
import Mathlib.Init.Data.Nat.Notation -- ℕ
import Mathlib.Data.Set.Lattice -- sUnion (⋃₀)
import Mathlib.Data.Set.Basic -- inter etc
import Std.Tactic.Basic -- byContra

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

------------------------------------------------------------------------------------------------------------------------
--                                                  Definitions                                                       --
------------------------------------------------------------------------------------------------------------------------

-- TODO: Define type alias for Set (Set α)
def IsPartitionOf (baseSet : Set α) (split : Set (Set α)) : Prop :=
    cells_are_pairwise_disjoint ∧ cells_are_non_empty ∧ union_of_cells_is_base_set
  where
    cells_are_pairwise_disjoint := ∀ x ∈ split, ∀ y ∈ split, x ≠ y → x ∩ y = ∅
    cells_are_non_empty := ∀ x ∈ split, x ≠ ∅
    union_of_cells_is_base_set := ⋃₀ split = baseSet

notation "Cells[ℕ]" => Set (Set ℕ)

-- TODO: Should we do {0, ..., n - 1} or {1, ..., n}?
def IsPartitionOfNatsUpTo (n : ℕ) (split : Cells[ℕ]) : Prop := IsPartitionOf (Set.Icc 1 n) split

def Pi (n : ℕ) : Set (Cells[ℕ]) := {split | IsPartitionOfNatsUpTo n split}

-- TODO: Clashes with dependent function type ("pi type")
notation "ℙ" => Pi

-- TODO: Better names for the transformations
def transformCell (cell : Set ℕ) (n : ℕ) : Set ℕ := cell ∪ {n}

def transformPartition (split : Cells[ℕ]) (cell : Set ℕ) (n : ℕ) : Cells[ℕ]
  := {transformCell cell n} ∪ (split \ {cell})

def partitionWithEmptyCell (split : Cells[ℕ]) : Cells[ℕ] := {∅} ∪ split

def toPartitionsOfNatsUpTo (partition : Cells[ℕ]) (n : ℕ) : Set (Cells[ℕ])
  := ⋃ cell ∈ partition, {transformPartition partition cell n}

def recursivePi (n : ℕ) : Set (Cells[ℕ]) := ⋃ partition ∈ ℙ (n - 1), toPartitionsOfNatsUpTo partition n

------------------------------------------------------------------------------------------------------------------------
--                                        recursivePi is a subset of Π' n                                             --
--                                                                                                                    --
--  To show this, we take the following steps:                                                                        --
--    - For p ∈ recursivePi n, we have cellsArePairwiseDisjoint, cellsAreNonEmpty, and unionOfCellsIsBaseSet.         --
------------------------------------------------------------------------------------------------------------------------

-- TODO: Fix looooong names and lines
lemma elements_of_recursivePi_have_cells_eq_to_partition_or_containing_n (n : ℕ) (split : Cells[ℕ])
  : split ∈ recursivePi n → ∀ cell ∈ split, ∃ partition ∈ ℙ (n - 1), ((n ∉ cell ∧ cell ∈ partition) ∨ (n ∈ cell ∧ cell \ {n} ∈ partition)) := by
    intro splitIsRecursive
    intro cell cell_in_split
    let split' := split \ {cell} ∪ {cell \ {n}}
    have split'_is_partition : split' ∈ ℙ (n - 1) := by
      have split'_cells_are_pairwise_disjoint : ∀ x ∈ split', ∀ y ∈ split', x ≠ y → x ∩ y = ∅ := by
        intro x h_x y h_y x_neq_y
        sorry
      sorry
    sorry

#print Exists.intro

-- TODO: Argue by contradiction
lemma elements_of_recursivePi_have_cellsArePairwiseDisjoint (n : ℕ) (split : Cells[ℕ])
  : split ∈ recursivePi n → ∀ x ∈ split, ∀ y ∈ split, x ≠ y → x ∩ y = ∅ := by
    intro splitIsRecursive
    intro x h_x y h_y x_neq_y
    by_contra h_contra
    --rw [Ne.def (x ∩ y) ∅] at h_contra
    sorry

#print Exists


theorem recursive_subset_pi (n : ℕ) : partition ∈ recursivePi n → partition ∈ ℙ n := by
  intro partitionIsRecursive
  have cellsArePairwiseDisjoint : ∀ x ∈ partition, ∀ y ∈ partition, x ≠ y → x ∩ y = ∅ := by
    apply Set.mem_sUnion.mp at partitionIsRecursive
    cases partitionIsRecursive with
      | intro smaller_partition h_smaller_partition =>
        sorry
  sorry

------------------------------------------------------------------------------------------------------------------------
--                                        ℙ n is a subset of recursivePi                                             --
------------------------------------------------------------------------------------------------------------------------

theorem partition_has_cell_containing_n (partition : Cells[ℕ]) (n : ℕ)
  : n ≥ 1 ∧ partition ∈ ℙ n → ∃ cell ∈ partition, n ∈ cell := by
    intro partitionIsPi
    have union_over_cells_is_base_set : ⋃₀ partition = (Set.Icc 1 n) := by
      apply partitionIsPi.right.right.right
    have n_is_in_union : n ∈ ⋃₀ partition := by
      rw [union_over_cells_is_base_set]
      apply Set.mem_Icc.mpr
      simp
      exact partitionIsPi.left
    apply Set.mem_sUnion.mp n_is_in_union

--theorem exists_cell_with_n (partition : Cells[ℕ]) (n : ℕ) : n ≥ 1 → ∃ cell ∈ partition, n ∈ cell := by
--  intro h
--  apply partition_has_cell_containing_n
--  constructor
--  sorry


theorem exists_exactly_one_cell_with_n (partition : Cells[ℕ]) (n : ℕ)
  : n ≥ 1 ∧ partition ∈ ℙ n → ∃ cell_n, {cell | n ∈ cell ∧ cell ∈ partition} = {cell_n} := by
    intro ⟨n_geq_1, partition_of_n⟩
    --have partition_has_cell_containing_n : exact partition_has_cell_containing_n partition n n_geq_1 partition_of_n


-- TODO: We must not remove the cell containing n but replace it by the 'inverse' of transformCell, i.e. the operation
--      that removes n from the cell.
theorem partition_without_cell_containing_n_is_partition (partition : Cells[ℕ]) (n : ℕ)
  : n ≥ 2 ∧ partition ∈ ℙ n → partition \ {cell | n ∈ cell ∧ cell ∈ partition} ∈ ℙ (n - 1) := by
    intro partitionIsPi
    have exists_cell_with_n : ∃ cell ∈ partition, n ∈ cell := by
      apply partition_has_cell_containing_n partition n
      have : n ≥ 1 := by cases partitionIsPi with
        | intro n_geq_2 => (have : 1 ≤ 2 := by decide); exact le_trans this n_geq_2
      exact ⟨this, partitionIsPi.right⟩
    have exists_exactly_one_cell_with_n : ∃ cell_n, {cell | n ∈ cell ∧ cell ∈ partition} = {cell_n} := by
      by_contra h_contra
      simp at h_contra
      absurd h_contra
      simp
      cases exists_cell_with_n with
        | intro cell_with_n h_cell_with_n =>
          use cell_with_n
          apply Set.ext
          sorry

    cases exists_exactly_one_cell_with_n with
      | intro cell_with_n h_cell_with_n =>
        rw [h_cell_with_n]
        sorry

#print Not

theorem pi_subset_recursive (n : ℕ) : partition ∈ ℙ n → partition ∈ recursivePi n := by
  intro partitionIsPi
  --apply Set.mem_iUnion
  sorry
  --apply Set.setOf_exists at partitionIsPi
  --sorry
  --use partition
  --split
  --exact partitionIsPi
  --apply Se

------------------------------------------------------------------------------------------------------------------------
--                                                Main Theorem                                                        --
------------------------------------------------------------------------------------------------------------------------

theorem Pi_is_recursive (n : ℕ) : ℙ n = recursivePi n := by
  apply Set.ext
  intro partition
  apply Iff.intro
  intro partitionIsPi
  exact pi_subset_recursive n partitionIsPi
  intro partitionIsRecursive
  exact recursive_subset_pi n partitionIsRecursive
