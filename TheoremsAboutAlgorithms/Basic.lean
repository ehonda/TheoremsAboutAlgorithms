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
def isPartitionOfNatsUpTo (n : ℕ) (split : Set (Set ℕ)) : Prop := isPartitionOf {x | x < n } split

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

theorem pi_subset_recursive (n : ℕ) : partition ∈ Π' n → partition ∈ recursivePi n := sorry

theorem recursive_subset_pi (n : ℕ) : partition ∈ recursivePi n → partition ∈ Π' n := sorry

theorem Pi_is_recursive (n : ℕ) : Π' n = recursivePi n := by
  apply Set.ext
  intro partition
  apply Iff.intro
  intro partitionIsPi
  exact pi_subset_recursive n partitionIsPi
  intro partitionIsRecursive
  exact recursive_subset_pi n partitionIsRecursive
