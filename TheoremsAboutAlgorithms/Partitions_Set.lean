import Mathlib.Init.Set
import Mathlib.Data.Set.Lattice

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

------------------------------------------------------------------------------------------------------------------------
--                                                  Definitions                                                       --
------------------------------------------------------------------------------------------------------------------------

universe u

-- Terminology:
--   * A cell of a type α is a subset of α
--   * A split of a type α is a collection of cells of α.
--   * A partition of a type α is a split of α such that the cells are pairwise disjoint and non-empty and their union
--     is the base set.
notation "Cell[" α "]" => Set α
-- TODO: How can we make it so in Lean infoview, terms of type Split[ℕ] are displayed not displayed as
--       Cell[Cell[ℕ]]?
notation:max "Split[" α "]" => Set (Cell[α])

-- TODO: Should these really be in the Set namespace (just to use dot notation)?
-- TODO: Maybe use Mathlib.Data.Set.Pairwise.Basic (Set.PairwiseDisjoint)
def Set.CellsArePairwiseDisjoint {α : Type u} (split : Split[α])
  : Prop := ∀ x ∈ split, ∀ y ∈ split, x ≠ y → x ∩ y = ∅

def Set.CellsAreNonEmpty {α : Type u} (split : Split[α])
  : Prop := ∀ x ∈ split, x.Nonempty

def Set.UnionOverSplitIsBaseSet {α : Type u} (split : Split[α]) (baseSet : Cell[α])
  : Prop := ⋃₀ split = baseSet

def Set.IsPartitionOf {α : Type u} (split : Split[α]) (baseSet : Cell[α])
  : Prop := split.CellsArePairwiseDisjoint ∧ split.CellsAreNonEmpty ∧ split.UnionOverSplitIsBaseSet baseSet

def Set.IsPartitionOfNatsUpTo (split : Split[ℕ]) (n : ℕ)
  : Prop := split.IsPartitionOf (Set.Ico 0 n)

def transformCell (cell : Cell[ℕ]) (n : ℕ) : Cell[ℕ] := insert n cell

-- TODO: More definitions

theorem transformCell_of_partition_is_disjoint_union
    {split : Split[ℕ]}
    {n : ℕ}
    (cell : Cell[ℕ])
    (h_cell : cell ∈ split)
    (h_partition : split.IsPartitionOfNatsUpTo n)
  : cell ∩ {n} = ∅ := by
    have h_union : ⋃₀ split = Set.Ico 0 n := h_partition.2.2
    have cell_subset : cell ⊆ Set.Ico 0 n := by
      sorry
    sorry
