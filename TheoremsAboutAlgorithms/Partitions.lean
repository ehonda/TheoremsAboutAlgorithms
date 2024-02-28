import Mathlib.Data.Setoid.Partition
import Init.Data.Fin.Basic

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

-- TODO: Is it better to use insert or the mathematical notation for set union using a singleton set (also for sdiff)?

-- TODO: Add comments everywhere (and especially to theorems).

-- Terminology:
--   * For any n : ℕ, a Cell n is a set of Fin n, i.e. a subset of the base set {0, 1, ..., n - 1}.
--   * For any n : ℕ, a Split n is a set of Cell n, i.e. a collection of subsets of the base set {0, 1, ..., n - 1}.
--
-- By using Fin n to represent the base set, we can use the definition Setoid.IsPartition from the standard library
-- to talk about partitions, which seems to present a nicer api than the one we would get by using Set ℕ and using
-- the classical definition of a partition, like e.g. the definition on wikipedia:
--
--    https://en.wikipedia.org/wiki/Partition_of_a_set#Definition_and_notation
abbrev Cell (n : ℕ) := Set (Fin n)
abbrev Split (n : ℕ) := Set (Cell n)

------------------------------------------------------------------------------------------------------------------------
--                                                  Cells                                                             --
------------------------------------------------------------------------------------------------------------------------

def Cell.castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := Fin.castSucc '' cell

-- TODO: Use a more descriptive name for this (and namespace it).
-- This is essentially cell ↦ {n} ∪ cell
def transformCell {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := (Cell.castSucc cell).insert (Fin.ofNat n)

-- TODO: Look for a nicer proof of this.
theorem transformCell_is_disjoint_insert {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.ofNat n} (Cell.castSucc cell) := by
    apply disjoint_iff.mpr
    simp [Cell.castSucc, Fin.castSucc, Fin.ofNat]
    intro k _
    apply lt_or_lt_iff_ne.mp
    have : k < n := by simp
    exact Or.inl this

------------------------------------------------------------------------------------------------------------------------
--                                                  Splits                                                            --
------------------------------------------------------------------------------------------------------------------------

def Split.castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Cell.castSucc '' split

def Split.removeCellAndCastSucc {n : ℕ} (split : Split n) (cell : Cell n) : Split (n + 1)
  := Split.castSucc (split \ singleton cell)

-- TODO: Use a more descriptive name for this (and namespace it).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {transformCell targetCell} ∪ (split \ {targetCell})
def transformSplit {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := (Split.removeCellAndCastSucc split targetCell).insert (transformCell targetCell)

theorem transformSplit_is_disjoint_insert {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Disjoint {transformCell targetCell} (Split.removeCellAndCastSucc split targetCell) := by
    apply disjoint_iff.mpr
    simp [Split.removeCellAndCastSucc, Fin.castSucc, Split.castSucc]
    intro cell _ _
    have h_k : ¬ (∀ (x : Fin (n + 1)), x ∈ Cell.castSucc cell ↔ x ∈ transformCell targetCell) := by
      simp [not_iff]
      exists (Fin.ofNat n)
      constructor
      · intro
        simp [transformCell]
        exact Set.mem_insert _ _
      · intro
        apply Set.disjoint_singleton_left.mp
        exact transformCell_is_disjoint_insert cell
    have := Set.ext_iff (s := Cell.castSucc cell) (t := transformCell targetCell)
    exact (not_congr this).mpr h_k

-- TODO: Find a better name for this (and namespace it).
def toSplitsWithN {n : ℕ} (split : Split n) : Set (Split (n + 1))
  := {transformSplit split cell | cell ∈ split.insert ∅}

------------------------------------------------------------------------------------------------------------------------
--                                              Partitions                                                            --
------------------------------------------------------------------------------------------------------------------------

def Split.IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

def partitions (n : ℕ) : Set (Split n)
  := {split | Split.IsPartition split}

notation "ℙ[" n "]" => partitions n

def recursivePartitions (n : ℕ) : Set (Split n)
  -- TODO: Needs helper function wrapping (toSplitsWithN split) in the appropriate Fin.cast to get
  --       Fin (n - 1 + 1) = Fin n in the types.
  --:= ⋃ partition ∈ ℙ[n - 1], toSplitsWithN partition
  := sorry

notation "ℙᵣ[" n "]" => recursivePartitions n
