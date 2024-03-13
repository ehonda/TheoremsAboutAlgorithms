import Mathlib.Data.Setoid.Partition
import Init.Data.Fin.Basic
import TheoremsAboutAlgorithms.Partitions.Cell
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Fin

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
--abbrev Cell (n : ℕ) := Set (Fin n)
--abbrev Split (n : ℕ) := Set (Cell n)

------------------------------------------------------------------------------------------------------------------------
--                                                  Cells                                                             --
------------------------------------------------------------------------------------------------------------------------

-- TODO: Maybe there's a more elegant way to use all those mapped functions
--def Cell.cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
--  := Fin.cast h '' cell
--
--theorem Cell.cast_Injective {n m : ℕ} (h : n = m) : Function.Injective (Cell.cast h) := by
--  apply Set.image_injective.mpr
--  exact Fin.cast_injective h
--
--theorem Cell.cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (Cell.cast h) := by
--  apply Set.image_surjective.mpr
--  exact Fin.cast_surjective h
--
--theorem Cell.cast_bijective {n m : ℕ} (h : n = m) : Function.Bijective (Cell.cast h)
--  := ⟨Cell.cast_Injective h, Cell.cast_surjective h⟩
--
--theorem Cell.cast_nonempty_iff {n m : ℕ} (h : n = m) (cell : Cell n)
--  : (cell.cast h).Nonempty ↔ cell.Nonempty := by simp [Cell.cast]
--
--def Cell.castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
--  := Fin.castSucc '' cell
--
---- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
--theorem Cell.castSucc_injective (n : ℕ) : Function.Injective (Cell.castSucc (n := n)) := by
--  apply Set.image_injective.mpr
--  exact Fin.castSucc_injective n

-- TODO: We don't have surjective / bijective for Cell.castSucc as Fin.last has no preimage. We could however prove it
--       for the restriction of Cell.castSucc to cells not containing n, but it's not clea how to best do that.
--
--       For now we use those "exists_preimage_of_ne_last" theorems to show what we need (but there could be better
--       abstractions to use).
--theorem Fin.castSucc_exists_preimage_of_ne_last {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ Fin.last n)
--  : ∃! (y : Fin n), y.castSucc = x := by
--    have h_x_lt_n : ↑x < n := by sorry
--    exists { val := x.val, isLt := h_x_lt_n }
--    simp
--    intro y hy
--    sorry
--    --have : castSucc x = { val := x.val, isLt := h_x_lt_n } := by sorry

--theorem Cell.castSucc_exists_preimage_of_ne_last
--    {n : ℕ}
--    (cell : Cell n)
--    (h : ∀ (x : Fin n), x ≠ Fin.last n)
--  : ∃! (cell' : Cell n), cell'.castSucc = cell := by


-- This is essentially cell ↦ {n} ∪ cell
def Cell.insertLast {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := cell.castSucc.insert (Fin.last n)

theorem Cell.insertLast_nonempty {n : ℕ} (cell : Cell n) : cell.insertLast.Nonempty
  := Set.insert_nonempty _ _

-- TODO: Look for a nicer proof of this.
theorem Cell.insertLast_is_disjoint_insert {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.last n} cell.castSucc := by
    apply disjoint_iff.mpr
    simp [Cell.castSucc, Fin.castSucc]
    intro k _
    apply lt_or_lt_iff_ne.mp
    have : k < n := by simp
    exact Or.inl this

------------------------------------------------------------------------------------------------------------------------
--                                                  Splits                                                            --
------------------------------------------------------------------------------------------------------------------------

def Split.cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Cell.cast h '' split

--theorem Split.cast_empty_not_mem_of_empty_not_mem {n m : ℕ} (h : n = m) (split : Split n) (h_empty : ∅ ∉ split)
--  : ∅ ∉ split.cast h := by
--    simp [Split.cast]
--    intro x h_x_mem
--    simp [Cell.cast]
--    -- TODO: Show ∅ ∉ split → x ∈ split → ¬x = ∅
--    sorry

theorem Split.cast_empty_not_mem_iff {n m : ℕ} (h : n = m) (split : Split n)
  : ∅ ∉ split.cast h ↔ ∅ ∉ split := by
    constructor <;> intro _ _ <;> simp [Split.cast, Cell.cast] at * <;> contradiction

theorem Split.cast_nonempty_iff {n m : ℕ} (h : n = m) (split : Split n)
  : (split.cast h).Nonempty ↔ split.Nonempty := by simp [Split.cast]

def Split.castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Cell.castSucc '' split

-- TODO: Fix naming elem -> mem
theorem Split.castSucc_empty_elem_iff {n : ℕ} (split : Split n)
  : ∅ ∈ split.castSucc ↔ ∅ ∈ split := by simp [Split.castSucc, Cell.castSucc]

def Split.removeCell {n : ℕ} (split : Split n) (cell : Cell n) : Split n
  := split \ singleton cell

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def Split.insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := (split.removeCell targetCell).castSucc.insert targetCell.insertLast

theorem Split.insertLastAt_castSucc_mem {n : ℕ} (split : Split n) (targetCell : Cell n)
  : targetCell.castSucc ∈ split.insertLastAt targetCell := by
    simp [Split.insertLastAt, Cell.insertLast]
    sorry

theorem Split.insertLastAt_Injective {n : ℕ} (split : Split n) : Function.Injective (split.insertLastAt) := by
  intro x y h
  --simp [Split.insertLastAt] at h
  have := (Set.ext_iff (s := split.insertLastAt x) (t := split.insertLastAt y)).mp h x.castSucc
  --simp [insertLastAt] at *
  sorry

theorem Split.insertLastAt_nonempty {n : ℕ} (split : Split n) (targetCell : Cell n)
  : (split.insertLastAt targetCell).Nonempty
    := Set.insert_nonempty _ _

-- TODO: Can we simplify this proof?
theorem Split.insertLastAt_empty_not_mem_of_empty_not_mem
  {n : ℕ} (split : Split n) (targetCell : Cell n) (h : ∅ ∉ split) : ∅ ∉ split.insertLastAt targetCell := by
    simp [Split.insertLastAt]
    intro h_empty_elem
    cases h_empty_elem with
      | inl h_elem_insertLast =>
        have := Cell.insertLast_nonempty targetCell
        -- TODO: There has to be an easier way to show Set.Nonempty x → ∅ = x → False
        rw [← h_elem_insertLast] at this
        cases this with
          | intro x h_x_elem_empty =>
            have := Set.mem_empty_iff_false x
            apply this.mp
            exact h_x_elem_empty
      | inr h_elem_removeCell =>
        simp [removeCell] at h_elem_removeCell
        have := Set.diff_subset split {targetCell}
        have h_empty_not_mem_diff := Set.not_mem_subset this h
        have h_empty_mem_diff := (Split.castSucc_empty_elem_iff (split \ {targetCell})).mp h_elem_removeCell
        contradiction

theorem Split.insertLastAt_is_disjoint_insert {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Disjoint {targetCell.insertLast} (split.removeCell targetCell).castSucc := by
    apply disjoint_iff.mpr
    simp [Split.removeCell, Split.castSucc, Fin.castSucc]
    intro cell _ _
    have h_k : ¬ (∀ (x : Fin (n + 1)), x ∈ cell.castSucc ↔ x ∈ targetCell.insertLast) := by
      simp [not_iff]
      exists (Fin.last n)
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

theorem Split.insertLast_nonempty_of_mem
  {n : ℕ}
  {split : Split n}
  {split' : Split (n + 1)}
  (h : split' ∈ Split.insertLast split)
  : split'.Nonempty := by
    simp [Split.insertLast] at h
    cases h with
      | intro cell h_cell =>
        rw [← h_cell.right]
        exact Split.insertLastAt_nonempty _ _

def Split.insertLast' {n : ℕ} (h : n > 0) (split : Split (n - 1)) : Set (Split n)
  := Split.cast (Nat.sub_add_cancel h) '' split.insertLast

theorem Split.insertLast'_nonempty_of_mem
  {n : ℕ}
  {h : n > 0}
  {split : Split (n - 1)}
  {split' : Split n}
  (h : split' ∈ Split.insertLast' h split)
  : split'.Nonempty := by
    simp [Split.insertLast'] at h
    cases h with
      | intro split'' h_split'' =>
        rw [← h_split''.right]
        have h_split''_nonempty : split''.Nonempty := Split.insertLast_nonempty_of_mem h_split''.left
        simp [Split.cast_nonempty_iff, h_split''_nonempty]

------------------------------------------------------------------------------------------------------------------------
--                                              Partitions                                                            --
------------------------------------------------------------------------------------------------------------------------

-- TODO: Namespace all of these

def Split.IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

-- TODO: Why can't we use e.g. partition.insertLast' for partition : Partition n?
def Partition (n : ℕ) := {split : Split n // split.IsPartition}

-- TODO: Can we provide this value constructively? How do we best encode that it contains Fin.last n?
def Partition.cellContainingLast {n : ℕ} (partition : Partition (n + 1)) : Cell (n + 1)
  := sorry
--  := let split := partition.val
--     let h := partition.property
--     h.right (Fin.last n) _

-- TODO: Should we somehow incorporate the subtype definition here?
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

-- TODO: Better name
-- TODO: Provide the version for Split 0 as well
theorem Partition.insertLast'_mem_mem_of_mem_of_last_not_mem
    {n : ℕ}
    {split : Split (n + 1)}
    {split' : Split (n + 2)}
    {cell : Cell (n + 1)}
    {h_pos : n + 2 > 0}
    (h_split : split' ∈ split.insertLast' h_pos)
    (h_mem : cell ∈ split)
    -- We need split : Split (n + 1) above so we can cast the Fin.last (otherwise we don't get n - 1 + 1 = n because
    -- we don't have n ≥ 1).
    -- TODO: This is wrong. Of course (Fin.last n) ∉ cell, because we only insert it via split.insertLastAt cell.
    --       What we could to is take a cell' ∈ split' where (Fin.last n) ∉ cell' and show that cell'.castPred is in
    --       split.
    (h_last_not_mem : (Fin.last n) ∉ cell)
  : cell.castSucc ∈ split' := by
    simp [Split.insertLast', Split.insertLast] at h_split
    cases h_split with
      | intro targetCell h_targetCell =>
        rw [← h_targetCell.right]
        simp at *
        sorry

-- Here we show that if we take a partition of Fin n and apply the operation partition.insertLast', then every resulting
-- split' is a partition of Fin (n + 1).
-- TODO: What namespace should this reside in?
theorem Partition.insertLast'_produces_partitions
    -- We use split : Split (n + 1) here because that's the form we need it in further down below
    {n : ℕ}
    {partition : Split n}
    {split : Split (n + 1)}
    {h_pos : n + 1 > 0}
    (h_partition : partition ∈ ℙ n)
    (h_split : split ∈ partition.insertLast' h_pos)
  : split.IsPartition := by
    have h_empty_not_mem : ∅ ∉ split := by
      simp [Split.insertLast', Split.insertLast] at h_split
      cases h_split with
        | intro cell h_cell =>
          have h_empty_not_mem_split'
            := Split.insertLastAt_empty_not_mem_of_empty_not_mem partition cell h_partition.left
          rw [← h_cell.right]
          exact (Split.cast_empty_not_mem_iff _ (partition.insertLastAt cell)).mpr h_empty_not_mem_split'
    have h_cover : ∀ (x : Fin (n + 1)), ∃! (cell : Cell (n + 1)), ∃! (_ : cell ∈ split), x ∈ cell := by
      intro x
      have := eq_or_ne x (Fin.last n)
      cases this with
        | inl h_eq =>
          -- TODO:
          sorry
        | inr h_ne =>
          simp [Split.insertLast', Split.insertLast] at h_split
          have x' := Fin.castPred x h_ne
          have := h_partition.right x'
          cases this with
            | intro cell h_cell =>
              simp at h_cell
              have cell' := Cell.castSucc cell
              exists cell'
              simp
              -- TODO: We need to show that casting cell yields cell' and have covering of x' and uniqueness follow from
              --       that.
              constructor
              · constructor
                · sorry
                · sorry
              · sorry
    exact And.intro h_empty_not_mem h_cover

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
          -- TODO: Plan:
          --        1. Take the split p' that results from removing the cell containing Fin.last m + 1 from split.
          --        2. Show that this split is a partition of m.
          --        3. Show that we get p from p' via the recursive construction.
          sorry

-- Maybe we can use Set.rangeSplitting here? It's noncomputable though.
theorem recursivePartitions_subset_partitions (n : ℕ) : ℙᵣ n ⊆ ℙ n := by
  intro split h
  cases n with
    | zero => simp [partitions_0, recursivePartitions] at * ; exact h
    | succ m =>
      -- TODO: Can we use something like Set.mem_range for this?
      cases h with
        | intro partitions h_partitions =>
          simp at h_partitions
          cases h_partitions.left with
            | intro partition h_partition =>
              -- TODO: Rewrite so it reads nicer
              have := h_partitions.right
              rw [← h_partition] at this
              simp [Set.mem_iUnion] at this
              exact Partition.insertLast'_produces_partitions this.left this.right

theorem partitions_eq_recursivePartitions (n : ℕ) : ℙ n = ℙᵣ n := by
  apply Set.eq_of_subset_of_subset
  · exact partitions_subset_recursivePartitions n
  · exact recursivePartitions_subset_partitions n
