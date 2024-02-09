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

-- Terminology:
--   * A cell of a type α is a subset of α
--   * A split of a type α is a collection of cells of α.
--   * A partition of a type α is a split of α such that the cells are pairwise disjoint and non-empty and their union
--     is the base set.
notation "Cell[" α "]" => Set α
-- TODO: How can we make it so in Lean infoview, terms of type Split[ℕ] are displayed not displayed as
--       Cell[Cell[ℕ]]?
notation:max "Split[" α "]" => Set (Set α)

def cellsArePairwiseDisjoint {α : Type} (split : Split[α]) : Prop :=
  ∀ x ∈ split, ∀ y ∈ split, x ≠ y → x ∩ y = ∅

-- TODO: Define type alias for Set (Set α)
def isPartitionOf (baseSet : Cell[α]) (split : Split[α]) : Prop :=
    cellsArePairwiseDisjoint split ∧ cellsAreNonEmpty ∧ unionOfSplitIsBaseSet
  where
    cellsAreNonEmpty := ∀ x ∈ split, x ≠ ∅
    unionOfSplitIsBaseSet := ⋃₀ split = baseSet

-- TODO: Should we do {0, ..., n - 1} or {1, ..., n}?
def isPartitionOfNatsUpTo (n : ℕ) (split : Split[ℕ]) : Prop := isPartitionOf (Set.Icc 1 n) split

def Pi (n : ℕ) : Set (Split[ℕ]) := {split | isPartitionOfNatsUpTo n split}

-- TODO: Clashes with dependent function type ("pi type")
notation "ℙ" => Pi

-- TODO: Better names for the transformations
def transformCell (cell : Cell[ℕ]) (n : ℕ) : Cell[ℕ] := cell ∪ {n}

def transformSplit (split : Split[ℕ]) (cell : Cell[ℕ]) (n : ℕ) : Split[ℕ]
  := {transformCell cell n} ∪ (split \ {cell})

def partitionWithEmptyCell (split : Split[ℕ]) : Split[ℕ] := {∅} ∪ split

def toPartitionsOfNatsUpTo (partition : Split[ℕ]) (n : ℕ) : Set (Split[ℕ])
  := ⋃ cell ∈ partition, {transformSplit partition cell n}

def recursivePi (n : ℕ) : Set (Split[ℕ]) := ⋃ partition ∈ ℙ (n - 1), toPartitionsOfNatsUpTo partition n

------------------------------------------------------------------------------------------------------------------------
--                                        Some basic facts we might need                                              --
------------------------------------------------------------------------------------------------------------------------

example (s : Cell[ℕ]) : s.Nonempty → s ≠ ∅ := by
  intro h
  exact Set.Nonempty.ne_empty h

example (n : ℕ) : Set.Nonempty {n} := by
  use n
  simp

lemma transform_partition_disjoint (split : Split[ℕ]) (cell : Cell[ℕ]) (n : ℕ)
  : Disjoint {transformCell cell n} (split \ {cell}) := by
    sorry

-- Here we show that the property that a split's cells are pairwise disjoint is preserved under the transformation
theorem pairwise_disjoint_after_transformation (split : Split[ℕ]) (targetCell : Cell[ℕ]) (n : ℕ)
  : (∀ cell ∈ split, cell ∩ {n} = ∅)
      ∧ (targetCell ∈ split)
      ∧ cellsArePairwiseDisjoint split
    → cellsArePairwiseDisjoint (transformSplit split targetCell n) := by
      -- Setup the hypotheses
      --     * A split is pairwise disjoint and none of it's cells contain n
      --     * We have an arbitrary cell x from the transformed split
      --     * We have an arbitrary cell y from the transformed split
      --     * x ≠ y
      --
      -- We then want to show that x ∩ y = ∅
      intro ⟨h_cell_inter_singleton_n, h_targetCell_in_split, h_split_pairwise_disjoint⟩
      intros x h_x y h_y h_neq
      -- We know that either x = targetCell ∨ x ≠ targetCell and consider both cases
      have := eq_or_ne x targetCell
      cases this with
        -- Case x = targetCell
        | inl h_x_eq =>
          -- We know that either y = targetCell ∨ y ≠ targetCell and consider both cases
          have := eq_or_ne y targetCell
          cases this with
            -- Case y = targetCell
            | inl h_y_eq =>
              -- We rewrite our hypothesis x ≠ y to targetCell ≠ targetCell and get a contradiction
              rw [h_x_eq, h_y_eq] at h_neq
              contradiction
            -- Case y ≠ targetCell
            | inr h_y_neq =>
              -- We consider the different cases for the transformed split. If x is part of the transformed split, we
              -- know that
              --    * Either x ∈ {transformCell targetCell n}, i.e. a split consisting of the single cell that is the
              --      result of transforming the target cell with n
              --    * Or x ∈ split \ {targetCell}, i.e. x is part of the split resulting from removing the target cell
              --      from the original split
              cases h_x with
                -- Case x ∈ {transformCell targetCell n}
                | inl h_x_in_transform =>
                  -- We rewrite x ∩ y = ∅ to (transformCell targetCell n) ∩ y = ∅, which we can because x is the only
                  -- cell of it's split and that cell is equal to (transformCell targetCell n)
                  rw [h_x_in_transform]
                  -- We have the same cases for cell y of the transformed split
                  cases h_y with
                    -- Case y ∈ {transformCell targetCell n}
                    | inl h_y_in_transform =>
                      -- We now know that x = transformCell targetCell n = y but have the hypothesis that x ≠ y, which
                      -- is a contradiction
                      simp at h_x_in_transform h_y_in_transform
                      rw [← h_y_in_transform] at h_x_in_transform
                      contradiction
                    -- Case y ∈ split \ {targetCell}
                    | inr h_y_in_split_sub =>
                      -- We know that y ∩ targetCell = ∅ because the original split is pairwise disjoint and the target
                      -- cell is part of the original split, and y is a cell of the original split that is not the
                      -- target cell
                      have h_y_inter_targetCell : y ∩ targetCell = ∅ := by
                        exact h_split_pairwise_disjoint y h_y_in_split_sub.left targetCell h_targetCell_in_split h_y_neq
                      -- We also know that y ∩ {n} = ∅ because none of the original cells contain n
                      have h_y_inter_singleton : y ∩ {n} = ∅ := by
                        exact h_cell_inter_singleton_n y h_y_in_split_sub.left
                      -- We thus have that
                      --      (transformCell targetCell n) ∩ y
                      --    = (targetCell ∪ {n}) ∩ y
                      --    = (targetCell ∩ y) ∪ ({n} ∩ y)
                      --    = ∅ ∪ ∅
                      --    = ∅
                      rw [
                        Set.inter_comm,
                        transformCell,
                        Set.inter_union_distrib_left,
                        h_y_inter_targetCell,
                        h_y_inter_singleton,
                        Set.empty_union]
                | inr h_x_in_split =>
                  -- TODO: Should be exactly the same as above, with roles of x and y reversed
                  -- TODO: Rewrite by appling tactics to the subgoals in parallel
                  sorry
        | inr h_x_neq =>
          -- TODO: Again, this should be the same as the case above, with reversed roles of x and y
          sorry

#print Set.Nonempty.ne_empty

def splitCellsContainingN (n : ℕ) (split : Split[ℕ]) : Split[ℕ] := {cell | n ∈ cell ∧ cell ∈ split}



lemma split_has_exactly_one_cell_containing_n (n : ℕ) (split : Split[ℕ])
  : split ∈ recursivePi n → ∃ cell ∈ split, splitCellsContainingN n split = {cell} := by
    intro splitIsRecursive
    sorry

------------------------------------------------------------------------------------------------------------------------
--                                        recursivePi is a subset of Π' n                                             --
--                                                                                                                    --
--  To show this, we take the following steps:                                                                        --
--    - For p ∈ recursivePi n, we have cellsArePairwiseDisjoint, cellsAreNonEmpty, and unionOfSplitIsBaseSet.         --
------------------------------------------------------------------------------------------------------------------------


def splitWithoutCellContainingN (n : ℕ) (split : Split[ℕ]) : Split[ℕ] := split \ {cell | n ∈ cell ∧ cell ∈ split}

def SplitWithoutCellContainingNIsPartition (n : ℕ) (split : Split[ℕ]) (partition : Split[ℕ]) : Prop :=
  splitWithoutCellContainingN n split = partition

def SplitWithoutCellContainingNIsSubsetOfPartition (n : ℕ) (split : Split[ℕ]) (partition : Split[ℕ]) : Prop :=
  splitWithoutCellContainingN n split ⊆ partition

-- TODO: Fix looooong names and lines
lemma split_without_cell_containing_n_lemma (n : ℕ) (split : Split[ℕ])
  : split ∈ recursivePi n → ∃ partition ∈ ℙ (n - 1), SplitWithoutCellContainingNIsPartition n split partition ∨ SplitWithoutCellContainingNIsSubsetOfPartition n split partition := by
    intro splitIsRecursive
    sorry

-- TODO: Fix looooong names and lines
lemma elements_of_recursivePi_have_cells_eq_to_partition_or_containing_n (n : ℕ) (split : Split[ℕ])
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
lemma elements_of_recursivePi_have_cellsArePairwiseDisjoint (n : ℕ) (split : Split[ℕ])
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

theorem partition_has_cell_containing_n (partition : Split[ℕ]) (n : ℕ)
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

--theorem exists_cell_with_n (partition : Split[ℕ]) (n : ℕ) : n ≥ 1 → ∃ cell ∈ partition, n ∈ cell := by
--  intro h
--  apply partition_has_cell_containing_n
--  constructor
--  sorry


theorem exists_exactly_one_cell_with_n (partition : Split[ℕ]) (n : ℕ)
  : n ≥ 1 ∧ partition ∈ ℙ n → ∃ cell_n, {cell | n ∈ cell ∧ cell ∈ partition} = {cell_n} := by
    intro ⟨n_geq_1, partition_of_n⟩
    --have partition_has_cell_containing_n : exact partition_has_cell_containing_n partition n n_geq_1 partition_of_n


-- TODO: We must not remove the cell containing n but replace it by the 'inverse' of transformCell, i.e. the operation
--      that removes n from the cell.
theorem partition_without_cell_containing_n_is_partition (partition : Split[ℕ]) (n : ℕ)
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
