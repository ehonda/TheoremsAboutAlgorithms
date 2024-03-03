import Mathlib.Data.Setoid.Partition
import Init.Data.Fin.Basic

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

-- TODO: Is it better to use insert or the mathematical notation for set union using a singleton set (also for sdiff)?

-- TODO: Add comments everywhere (and especially to theorems).

-- TODO: Use namespaces and group definitions and theorems accordingly, to not have to write explicit Cell. and Split.
--       everywhere.

-- Terminology:
--   * For any n : ℕ, a Cell n is a set of Fin n, i.e. a subset of the base set {0, 1, ..., n - 1}.
--   * For any n : ℕ, a Split n is a set of Cell n, i.e. a collection of subsets of the base set {0, 1, ..., n - 1}.
--     Note that these don't have to be disjoint, so this is not the same as a partition of the base set.
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

-- TODO: Maybe there's a more elegant way to use all those mapped functions
def Cell.cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  := Fin.cast h '' cell

def Cell.castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := Fin.castSucc '' cell

-- This is essentially cell ↦ {n} ∪ cell
def Cell.insertLast {n : ℕ} (cell : Cell n) : Cell (n + 1)
  -- TODO: Maybe use Fin.last n instead of Fin.ofNat n
  := cell.castSucc.insert (Fin.ofNat n)

-- TODO: Look for a nicer proof of this.
theorem Cell.insertLast_is_disjoint_insert {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.ofNat n} cell.castSucc := by
    apply disjoint_iff.mpr
    simp [Cell.castSucc, Fin.castSucc, Fin.ofNat]
    intro k _
    apply lt_or_lt_iff_ne.mp
    have : k < n := by simp
    exact Or.inl this

------------------------------------------------------------------------------------------------------------------------
--                                                  Splits                                                            --
------------------------------------------------------------------------------------------------------------------------

def Split.cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Cell.cast h '' split

def Split.castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Cell.castSucc '' split

def Split.removeCell {n : ℕ} (split : Split n) (cell : Cell n) : Split n
  := split \ singleton cell

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def Split.insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := (split.removeCell targetCell).castSucc.insert targetCell.insertLast

theorem Split.insertLastAt_is_disjoint_insert {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Disjoint {targetCell.insertLast} (split.removeCell targetCell).castSucc := by
    apply disjoint_iff.mpr
    simp [Split.removeCell, Split.castSucc, Fin.castSucc]
    intro cell _ _
    have h_k : ¬ (∀ (x : Fin (n + 1)), x ∈ cell.castSucc ↔ x ∈ targetCell.insertLast) := by
      simp [not_iff]
      exists (Fin.ofNat n)
      constructor
      · intro
        simp [Cell.insertLast]
        exact Set.mem_insert _ _
      · intro
        apply Set.disjoint_singleton_left.mp
        exact Cell.insertLast_is_disjoint_insert cell
    have := Set.ext_iff (s := cell.castSucc) (t := targetCell.insertLast)
    exact (not_congr this).mpr h_k

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- TODO: Do we even need this if we have the version below?
def Split.insertLast {n : ℕ} (split : Split n) : Set (Split (n + 1))
  := {split.insertLastAt cell | cell ∈ split.insert ∅}

def Split.insertLast' {n : ℕ} (h : n > 0) (split : Split (n - 1)) : Set (Split n)
  := Split.cast (Nat.sub_add_cancel h) '' split.insertLast

------------------------------------------------------------------------------------------------------------------------
--                                              Partitions                                                            --
------------------------------------------------------------------------------------------------------------------------

def Split.IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

def partitions (n : ℕ) : Set (Split n)
  := {split | split.IsPartition}

-- TODO: Improve this proof and add comments
theorem partitions_0 : partitions 0 = {∅} := by
  apply Set.eq_of_subset_of_subset
  · intro split h
    simp
    have := eq_or_ne split ∅
    cases this with
      | inl h_eq => exact h_eq
      | inr h_ne =>
        have := Set.nonempty_iff_ne_empty.mpr h_ne
        cases this with
          | intro cell h_cell =>
            have := eq_or_ne cell ∅
            cases this with
              | inl h_eq =>
                cases h with
                  | intro h_empty _ => rw [h_eq] at h_cell ; contradiction
              | inr h_ne' =>
                have := Set.nonempty_iff_ne_empty.mpr h_ne'
                cases this with
                  | intro fin _ => apply Fin.elim0 fin
  · intro split h
    simp at h
    have h_empty_not_mem : ∅ ∉ split := by simp [h]
    have h_cover : ∀ (x : Fin 0), ∃! (cell : Cell 0), ∃! (_ : cell ∈ split), x ∈ cell := by
      intro x
      apply Fin.elim0 x
    exact And.intro h_empty_not_mem h_cover

abbrev ℙ (n : ℕ) := partitions n

def recursivePartitions (n : ℕ) : Set (Split n)
  := match n with
    | 0 => {∅}
    | m + 1 => ⋃ partition ∈ ℙ m, partition.insertLast' (Nat.succ_pos m)

abbrev ℙᵣ (n : ℕ) := recursivePartitions n

theorem partitions_subset_recursivePartitions (n : ℕ) : ℙ n ⊆ ℙᵣ n := by
  intro split h
  cases n with
    | zero => simp [partitions_0] at h ; exact h
    | succ m =>
      have : ∃! (cell : Cell (m + 1)), ∃! (h_cell : cell ∈ split), (Fin.ofNat m + 1) ∈ cell := by
        cases h with
          | intro _ h_cover => exact h_cover (Fin.ofNat m + 1)
      cases this with
        | intro cell h_cell_unique =>
          sorry

theorem partitions_eq_recursivePartitions (n : ℕ) : ℙ n = ℙᵣ n := by
  sorry
