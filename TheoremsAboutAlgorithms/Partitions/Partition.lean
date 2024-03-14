import TheoremsAboutAlgorithms.Partitions.Cell
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Fin
import TheoremsAboutAlgorithms.Partitions.Split

namespace Partition

-- TODO: Why can't we use e.g. partition.insertLast' for partition : Partition n?
def Partition (n : ℕ) := {split : Split n // split.IsPartition}

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
theorem insertLast'_mem_mem_of_mem_of_last_not_mem
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
theorem insertLast'_produces_partitions
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
              exact insertLast'_produces_partitions this.left this.right

theorem partitions_eq_recursivePartitions (n : ℕ) : ℙ n = ℙᵣ n := by
  apply Set.eq_of_subset_of_subset
  · exact partitions_subset_recursivePartitions n
  · exact recursivePartitions_subset_partitions n

end Partition
