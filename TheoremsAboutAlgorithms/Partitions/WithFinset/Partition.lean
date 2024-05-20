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
          obtain ⟨targetCell, _, insertLastAt_partition_targetCell_eq_split⟩
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
          simp [Split.insertLastAt] at insertLastAt_partition_targetCell_eq_split
          split_ands
          · split
            case _ cell'_eq_targetCell =>
              simp [CoeDep.coe, insertLastAt_partition_targetCell_eq_split.symm]
              left
              rw [cell'_eq_targetCell]
            case _ cell'_ne_targetCell =>
              simp [CoeDep.coe, insertLastAt_partition_targetCell_eq_split.symm]
              right
              simp [Split.castSucc, Cell.castSuccEmbedding]
              constructor
              · simp [Cell.castSucc, cell'_ne_targetCell]
              · exists cell'
          · split
            case _ cell'_eq_targetCell =>
              simp [CoeDep.coe, Cell.insertLast]
              right
              subst cell' cell''
              exact Cell.mem_castSucc_of_ne_last_of_castPred_mem x_ne_last castPred_x_mem_cell''
            case _ cell'_ne_targetCell =>
              simp [CoeDep.coe, Cell.castSucc]
              subst cell''
              exists Fin.castPred x x_ne_last
          · intro otherCell otherCell_mem_split x_mem_otherCell
            split
            case _ cell'_eq_targetCell =>
              simp [CoeDep.coe]
              simp [Split.insertEmpty] at targetCell_mem_insertEmpty_partition
              cases targetCell_mem_insertEmpty_partition with
                | inl targetCell_eq_empty =>
                  subst cell' cell''
                  rw [targetCell_eq_empty] at cell'_mem_partition
                  absurd cell'_mem_partition
                  -- TODO: We would like to do `exact partition_mem_partitions.left` here but it gives us:
                  --
                  --       ```
                  --       type mismatch
                  --         partition_mem_partitions.left
                  --       has type
                  --         @EmptyCollection.emptyCollection (Set (Fin n)) Set.instEmptyCollectionSet ∉
                  --           ↑(Finset.map Finset.toSetEmbedding partition) : Prop
                  --       but is expected to have type
                  --         @EmptyCollection.emptyCollection (Cell n) Finset.instEmptyCollectionFinset ∉ partition : Prop
                  --       ```
                  --
                  --       How can we make it work?
                  have := partition_mem_partitions.left
                  simp [Finset.toSetEmbedding] at this
                  exact this
                | inr targetCell_mem_partition =>
                  rw [← insertLastAt_partition_targetCell_eq_split] at otherCell_mem_split
                  set otherCell' := Split.downward
                      partition
                      ⟨targetCell, targetCell_mem_partition⟩
                      ⟨otherCell, otherCell_mem_split⟩
                    with otherCell'_def
                  subst cell' cell''
                  unfold Split.downward at otherCell'_def
                  split at otherCell'_def
                  case _ => assumption
                  case _ otherCell'_ne_targetCell =>
                    -- TODO: This whole prove is very messy, there should be an easier way
                    simp at otherCell'_ne_targetCell
                    simp [otherCell'_ne_targetCell, Split.castSucc, Cell.castSuccEmbedding] at otherCell_mem_split
                    obtain ⟨otherCell_ne_castSucc_targetCell, otherCell'', otherCell''_mem_partition, castSucc_otherCell''_eq_otherCell⟩
                      := otherCell_mem_split
                    -- TODO: Maybe it's not ideal that we use the `Setoid.IsPartition` definition because it e.g. gives
                    --       us `∀ (y : Set (Fin n))` on the unique property and thus we only get that the `toSet` of
                    --       the finsets are equal (which might not be strong enough?). So maybe we just have to
                    --       duplicate the definition in terms of `Finset`.
                    have toSet_otherCell''_eq_toSet_targetCell : (otherCell'' : Set (Fin n)) = targetCell := by
                      have x'_mem_otherCell'' : x' ∈ otherCell'' := by
                        rw [← castSucc_otherCell''_eq_otherCell] at x_mem_otherCell
                        exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                      apply cell'_unique otherCell''
                      simp
                      constructor
                      · exists otherCell''
                      · exact x'_mem_otherCell''
                    have otherCell''_eq_targetCell : otherCell'' = targetCell := by
                      apply Finset.toSetEmbedding.injective
                      exact toSet_otherCell''_eq_toSet_targetCell
                    -- TODO: There has to be a more direct way to get the contradicition here
                    absurd castSucc_otherCell''_eq_otherCell
                    rw [otherCell''_eq_targetCell]
                    intro castSucc_targetCell_eq_otherCell
                    rw [castSucc_targetCell_eq_otherCell] at otherCell_ne_castSucc_targetCell
                    contradiction
            case _ cell'_ne_targetCell =>
              subst cell''
              rw [← insertLastAt_partition_targetCell_eq_split] at otherCell_mem_split
              simp at otherCell_mem_split
              -- TODO: This and the `cases targetCell_mem_insertEmpty_partition` we have done above as well, we should
              --       abstract this away or provide a helper theorem or something
              cases otherCell_mem_split with
                | inl otherCell_eq_insertLast_targetCell =>
                  simp [Cell.insertLast] at otherCell_eq_insertLast_targetCell
                  simp [Split.insertEmpty] at targetCell_mem_insertEmpty_partition
                  cases targetCell_mem_insertEmpty_partition with
                    | inl targetCell_eq_empty =>
                      subst targetCell
                      simp [Cell.castSucc] at otherCell_eq_insertLast_targetCell
                      rw [otherCell_eq_insertLast_targetCell] at x_mem_otherCell
                      absurd x_ne_last
                      exact Finset.eq_of_mem_singleton x_mem_otherCell
                    | inr targetCell_mem_partition =>
                      absurd cell'_ne_targetCell
                      apply Finset.toSetEmbedding.injective
                      have : (targetCell : Set (Fin n)) = cell' := by
                        apply cell'_unique targetCell
                        simp
                        constructor
                        · exists targetCell
                        · rw [otherCell_eq_insertLast_targetCell] at x_mem_otherCell
                          simp [x_ne_last] at x_mem_otherCell
                          exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                      exact this.symm
                | inr otherCell_mem_partition =>
                  simp [Split.castSucc, Cell.castSuccEmbedding] at otherCell_mem_partition
                  obtain ⟨_, otherCell', otherCell'_mem_partition, castSucc_otherCell'_eq_otherCell⟩
                    := otherCell_mem_partition
                  have : otherCell' = cell' := by
                    apply Finset.toSetEmbedding.injective
                    have : (otherCell' : Set (Fin n)) = cell' := by
                      apply cell'_unique otherCell'
                      simp
                      constructor
                      · exists otherCell'
                      · rw [← castSucc_otherCell'_eq_otherCell] at x_mem_otherCell
                        exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                    exact this
                  subst otherCell'
                  simp [CoeDep.coe]
                  exact castSucc_otherCell'_eq_otherCell.symm

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
