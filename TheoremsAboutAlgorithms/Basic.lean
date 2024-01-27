import Init.Core -- Iff
import Mathlib.Init.Set -- Set
import Mathlib.Init.Data.Nat.Notation -- ℕ
import Mathlib.Data.Set.Lattice -- sUnion (⋃₀)

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

-- TODO: Define type alias for Set (Set α)
def isPartitionOf (baseSet : Set α) (split : Set (Set α)) : Prop :=
    cellsArePairwiseDisjoint ∧ cellsAreNonEmpty ∧ unionOfCellsIsBaseSet
  where
    cellsArePairwiseDisjoint := ∀ x ∈ split, ∀ y ∈ split, x ≠ y → x ∩ y = ∅
    cellsAreNonEmpty := ∀ x ∈ split, x ≠ ∅
    unionOfCellsIsBaseSet := ⋃₀ split = baseSet

-- TODO: Should we do {0, ..., n - 1} or {1, ..., n}?
def isPartitionOfNatsUpTo (n : ℕ) (split : Set (Set ℕ)) : Prop := isPartitionOf (Set.Icc 1 n) split

def Pi (n : ℕ) : Set (Set (Set ℕ)) := {split | isPartitionOfNatsUpTo n split}

-- TODO: Clashes with dependent function type ("pi type")
notation "Π'" => Pi

-- TODO: Better names for the transformations
def transformCell (cell : Set ℕ) (n : ℕ) : Set ℕ := cell ∪ {n}

def transformPartition (split : Set (Set ℕ)) (cell : Set ℕ) (n : ℕ) : Set (Set ℕ)
  := {transformCell cell n} ∪ (split \ {cell})

def partitionWithEmptyCell (split : Set (Set ℕ)) : Set (Set ℕ) := {∅} ∪ split

def toPartitionsOfNatsUpTo (partition : Set (Set ℕ)) (n : ℕ) : Set (Set (Set ℕ))
  := ⋃ cell ∈ partition, {transformPartition partition cell n}

def recursivePi (n : ℕ) : Set (Set (Set ℕ)) := ⋃ partition ∈ Π' (n - 1), toPartitionsOfNatsUpTo partition n

theorem partition_has_cell_containing_n (partition : Set (Set ℕ)) (n : ℕ)
  : n ≥ 1 ∧ partition ∈ Π' n → ∃ cell ∈ partition, n ∈ cell := by
    intro partitionIsPi
    have union_over_cells_is_base_set : ⋃₀ partition = (Set.Icc 1 n) := by
      apply partitionIsPi.right.right.right
    have n_is_in_union : n ∈ ⋃₀ partition := by
      rw [union_over_cells_is_base_set]
      apply Set.mem_Icc.mpr
      simp
      exact partitionIsPi.left
    apply Set.mem_sUnion.mp n_is_in_union

theorem pi_subset_recursive (n : ℕ) : partition ∈ Π' n → partition ∈ recursivePi n := by
  intro partitionIsPi
  --apply Set.mem_iUnion
  sorry
  --apply Set.setOf_exists at partitionIsPi
  --sorry
  --use partition
  --split
  --exact partitionIsPi
  --apply Se

theorem recursive_subset_pi (n : ℕ) : partition ∈ recursivePi n → partition ∈ Π' n := sorry

theorem Pi_is_recursive (n : ℕ) : Π' n = recursivePi n := by
  apply Set.ext
  intro partition
  apply Iff.intro
  intro partitionIsPi
  exact pi_subset_recursive n partitionIsPi
  intro partitionIsRecursive
  exact recursive_subset_pi n partitionIsRecursive
