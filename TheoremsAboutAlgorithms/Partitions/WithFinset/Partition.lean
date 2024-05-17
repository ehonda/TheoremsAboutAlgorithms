import TheoremsAboutAlgorithms.Partitions.WithFinset.Split.Basic
import TheoremsAboutAlgorithms.Partitions.WithFinset.Split.UpwardDownward

namespace Partition

-- TODO: Do we want to use this anywhere?
def Partition (n : ℕ) := {split : Split n // split.IsPartition}

-- TODO: Should we somehow incorporate the subtype definition here?
def partitions (n : ℕ) : Set (Split n)
  := {split | split.IsPartition}

abbrev ℙ (n : ℕ) := partitions n

theorem partitions_0 : partitions 0 = {∅} := by
  apply Set.eq_of_subset_of_subset
  · intro split split_mem_singleton_empty
    simp
    cases split.eq_empty_or_nonempty with
      | inl => assumption;
      | inr split_nonempty =>
        obtain ⟨cell, cell_mem_split⟩ := split_nonempty
        cases cell.eq_empty_or_nonempty with
          | inl cell_eq_empty =>
            -- TODO: Can this be a oneliner absurd?
            absurd Split.nonempty_of_mem_partition split_mem_singleton_empty cell_mem_split
            simp
            exact cell_eq_empty
          | inr cell_nonempty =>
            obtain ⟨x⟩ := cell_nonempty
            apply x.elim0
  · intro split split_mem_partitions_0
    simp at split_mem_partitions_0
    constructor
    · rw [split_mem_partitions_0]; simp [Finset.toSetEmbedding]
    · intro x; apply x.elim0

def recursivePartitions (n : ℕ) : Set (Split n)
  := match n with
    | 0 => {∅}
    | m + 1 => ⋃ partition ∈ ℙ m, partition.insertLast

abbrev ℙᵣ (n : ℕ) := recursivePartitions n

-- TODO: This name is probably not quite right
theorem isPartition_of_mem_insertLast_of_isPartition
    -- We use split : Split (n + 1) here because that's the form we need it in further down below
    {n : ℕ}
    {partition : Split n}
    {split : Split (n + 1)}
    (partition_mem_partitions : partition ∈ ℙ n)
    (split_mem_insertLast_partition : split ∈ partition.insertLast)
  : split.IsPartition := by
    constructor
    · simp [Finset.toSetEmbedding]
      intro empty_mem_split
      obtain ⟨targetCell, targetCell_mem_insertEmpty_partition, insertLastAt_partition_targetCell_eq_split⟩
        := split_mem_insertLast_partition
      simp [Split.insertLastAt] at insertLastAt_partition_targetCell_eq_split
      rw [← insertLastAt_partition_targetCell_eq_split] at empty_mem_split
      simp at empty_mem_split
      cases empty_mem_split with
        | inl empty_eq_insertLast_targetCell =>
          simp [Cell.insertLast] at empty_eq_insertLast_targetCell
          -- TODO: How can we 1-line this such that the goal is closed immediately instead of giving us `⊢ ¬False`
          absurd (Finset.insert_ne_empty _ _).symm empty_eq_insertLast_targetCell
          trivial
        -- We don't define `partition' := partition.erase targetCell` directly because we don't use it directly, we only
        -- use it for the consice naming
        | inr empty_mem_castSucc_partition' =>
          apply (Split.empty_mem_castSucc_iff_empty_mem _).mp at empty_mem_castSucc_partition'
          simp [Finset.mem_erase] at empty_mem_castSucc_partition'
          obtain ⟨_, empty_mem_partition⟩ := empty_mem_castSucc_partition'
          absurd partition_mem_partitions.left
          simp [Finset.toSetEmbedding]
          exact empty_mem_partition
    · intro x
      cases Decidable.eq_or_ne x (Fin.last _) with
        | inl x_eq_last =>
          simp [Split.insertLast, Finset.toSetEmbedding] at *
          -- TODO: We use this in a sibling goal as well, move further up so we only have to do this once
          obtain ⟨targetCell, targetCell_mem_insertEmpty_partition, insertLastAt_partition_targetCell_eq_split⟩
            := split_mem_insertLast_partition
          exists targetCell.insertLast
          simp
          split_ands
          · simp [insertLastAt_partition_targetCell_eq_split.symm, Split.insertLastAt]
          · simp [x_eq_last, Cell.insertLast]
          · intro cell cell_mem_split x_mem_cell
            simp [insertLastAt_partition_targetCell_eq_split.symm, Split.insertLastAt] at cell_mem_split
            cases cell_mem_split with
              | inl => assumption
              | inr cell_mem_partition =>
                rw [x_eq_last] at x_mem_cell
                -- TODO: 1-line this
                absurd Split.last_not_mem_of_mem_castSucc cell_mem_partition x_mem_cell
                trivial
        | inr x_ne_last =>
          let x' := x.castPred x_ne_last
          -- TODO: Here we get `cell' : Set (Fin n)` but we need `cell' : Cell n` to be able to use `Split.upward`. We
          --      untangle this manually here but maybe we should provide a theorem that gets us there nicely. This is
          --      very technical / finicky.
          obtain ⟨cell'', x'_mem_cell', cell'_unique⟩ := partition_mem_partitions.right x'
          simp [Finset.toSetEmbedding] at x'_mem_cell'
          obtain ⟨⟨cell', cell'_mem_partition, cell'_eq_cell''⟩, castPred_x_mem_cell''⟩ := x'_mem_cell'
          -- TODO: We use this in a sibling goal as well, move further up so we only have to do this once
          obtain ⟨targetCell, targetCell_mem_insertEmpty_partition, insertLastAt_partition_targetCell_eq_split⟩
            := split_mem_insertLast_partition
          exists @Split.upward _ partition targetCell ⟨cell', cell'_mem_partition⟩
          simp [Finset.toSetEmbedding, Split.upward]
          split_ands
          -- TODO: Finish this proof
          · sorry
          · sorry
          · sorry

theorem partitions_subset_recursivePartitions (n : ℕ) : ℙ n ⊆ ℙᵣ n := by
  sorry
  -- intro split h
  -- cases n with
  --   | zero => simp [partitions_0] at h ; exact h
  --   | succ m =>
  --     have : ∃! (cell : Cell (m + 1)), ∃! (h_cell : cell ∈ split), (Fin.ofNat m + 1) ∈ cell := by
  --       cases h with
  --         | intro _ h_cover => exact h_cover (Fin.ofNat m + 1)
  --     cases this with
  --       | intro cell h_cell_unique =>
  --         -- TODO: Plan:
  --         --        1. Take the split p' that results from removing the cell containing Fin.last m + 1 from split.
  --         --        2. Show that this split is a partition of m.
  --         --        3. Show that we get p from p' via the recursive construction.
  --         sorry

-- Maybe we can use Set.rangeSplitting here? It's noncomputable though.
theorem recursivePartitions_subset_partitions (n : ℕ) : ℙᵣ n ⊆ ℙ n := by
  sorry
  -- intro split h
  -- cases n with
  --   | zero => simp [partitions_0, recursivePartitions] at * ; exact h
  --   | succ m =>
  --     -- TODO: Can we use something like Set.mem_range for this?
  --     cases h with
  --       | intro partitions h_partitions =>
  --         simp at h_partitions
  --         cases h_partitions.left with
  --           | intro partition h_partition =>
  --             -- TODO: Rewrite so it reads nicer
  --             have := h_partitions.right
  --             rw [← h_partition] at this
  --             simp [Set.mem_iUnion] at this
  --             exact insertLast'_produces_partitions this.left this.right

theorem partitions_eq_recursivePartitions (n : ℕ) : ℙ n = ℙᵣ n := by
  apply Set.eq_of_subset_of_subset
  · exact partitions_subset_recursivePartitions n
  · exact recursivePartitions_subset_partitions n

end Partition
