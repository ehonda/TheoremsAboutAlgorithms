import Mathlib.Init.Set -- Set
import Mathlib.Init.Data.Nat.Notation -- ℕ
import Mathlib.Data.Set.Lattice -- sUnion (⋃₀)

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

theorem trivial_1 :  1 = 1 := rfl

--theorem Pi_is_recursive (n : ℕ)
--  : Π' n = ⋃ partition ∈ Π' (n - 1), ⋃ cell ∈ partitionWithEmptyCell partition, transformPartition partition cell n := by sorry
