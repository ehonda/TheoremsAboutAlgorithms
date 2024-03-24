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
    -- TODO: eq_or_ne uses em, maybe there's a constructive way to do this? Maybe Decidable.eq_or_ne? Or another route?
    --       Maybe we can use Finset.decidableEq as well?
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
      simp [Split.insertLast', Split.insertLast] at h_split
      cases h_split with
        | intro targetCell h_targetCell =>
          have := Decidable.eq_or_ne x (Fin.last n)
          cases this with
            | inl h_eq =>
              -- Here we have x = Fin.last n. We know that n is not in any cell of partition, which we can use to show
              -- that it must be in the result of the insert operation.
              have := Split.insertLastAt_unique_cell_last_mem partition targetCell
              cases this with
                | intro cell h_cell =>
                  simp [Split.InSplitInsertLastAtAndContainsLast] at *
                  rw [← h_targetCell.right]
                  have h_cell_mem_split : cell ∈ split := by
                    rw [← h_targetCell.right]
                    apply (Split.cast_mem_iff (partition.insertLastAt targetCell) cell).mpr
                    exact h_cell.left.left
                  have h_last_mem_cell : Fin.last n ∈ cell := h_cell.left.right
                  rw [h_targetCell.right, h_eq]
                  apply ExistsUnique.intro cell
                  · exact And.intro h_cell_mem_split h_last_mem_cell
                  · intro otherCell h_otherCell
                    have otherCell_mem_split' : otherCell ∈ Split.insertLastAt partition targetCell := by
                      rw [← h_targetCell.right] at h_otherCell
                      apply (Split.cast_mem_iff (partition.insertLastAt targetCell) otherCell).mp
                      exact h_otherCell.left
                    exact h_cell.right _ otherCell_mem_split' h_otherCell.right
            | inr h_ne =>
              -- Here we have x ≠ Fin.last n. We know that x is in some cell of partition.
              -- If that cell is not the targetCell, we can use castSucc on it and have our unique cell that contains x.
              -- If it is the targetCell, maybe we can do the following: Remove n from the targetCell:
              --   * If the resulting cell is not empty, we have a preimage and can use that to show uniqueness
              --     * TODO: Show that for any cell in Split.insertLastAt, if we remove n from it, we get a cell in the
              --            original split (if the result is not empty)
              --   * If the resulting cell is empty, ... (TODO)
              -- TODO: How can we use x' := x.castPred h_ne here?
              have := h_partition.right (x.castPred h_ne)
              cases this with
                | intro cell' h_cell' =>
                  simp at h_cell'
                  -- TODO: Probably place that higher up the stack to get rid of that `∃! cell x_1, x ∈ cell` earlier
                  simp
                  have := eq_or_ne cell' targetCell
                  cases this with
                    | inl h_eq_targetCell =>
                      simp [Set.insert] at h_targetCell
                      cases h_targetCell.left with
                        | inl h_empty =>
                          have := Set.not_mem_empty (x.castPred h_ne)
                          have : x.castPred h_ne ∈ ∅ := by
                            rw [h_eq_targetCell, h_empty] at h_cell'
                            exact h_cell'.left.right
                          contradiction
                        | inr h_targetCell_mem_partition =>
                          apply ExistsUnique.intro (Cell.insertLast cell')
                          · have cell'_mem_split : (Cell.insertLast cell') ∈ split := by
                              rw [← h_targetCell.right]
                              apply (Split.cast_mem_iff (partition.insertLastAt targetCell) (Cell.insertLast cell')).mpr
                              simp [Split.insertLastAt, h_eq_targetCell, Set.insert]
                            have x_mem_cell' : x ∈ (Cell.insertLast cell') := by
                              simp [Cell.insertLast, Set.insert, Cell.castSucc]
                              right
                              exists x.castPred h_ne
                              constructor
                              · exact h_cell'.left.right
                              · exact Fin.castSucc_castPred _ _
                            exact And.intro cell'_mem_split x_mem_cell'
                          · intro otherCell h_otherCell
                            have otherCell_mem_split' : otherCell ∈ Split.insertLastAt partition targetCell := by
                              rw [← h_targetCell.right] at h_otherCell
                              apply (Split.cast_mem_iff (partition.insertLastAt targetCell) otherCell).mp
                              exact h_otherCell.left
                            -- TODO: Again, this is the same situation as below
                            sorry
                    | inr h_ne_targetCell =>
                      -- TODO: How can we use cell := Cell.castSucc cell' here?
                      apply ExistsUnique.intro (Cell.castSucc cell')
                      · have cell_mem_split : (Cell.castSucc cell') ∈ split := by
                          rw [← h_targetCell.right]
                          apply (Split.cast_mem_iff (partition.insertLastAt targetCell) (Cell.castSucc cell')).mpr
                          exact Split.insertLastAt_castSucc_mem_of_mem_of_ne_targetCell
                            h_cell'.left.left h_ne_targetCell
                        have x_mem_cell : x ∈ (Cell.castSucc cell') := by
                          simp [Cell.castSucc]
                          exists x.castPred h_ne
                          constructor
                          · exact h_cell'.left.right
                          · exact Fin.castSucc_castPred _ _
                        exact And.intro cell_mem_split x_mem_cell
                      · intro otherCell h_otherCell
                        have otherCell_mem_split' : otherCell ∈ Split.insertLastAt partition targetCell := by
                          rw [← h_targetCell.right] at h_otherCell
                          apply (Split.cast_mem_iff (partition.insertLastAt targetCell) otherCell).mp
                          exact h_otherCell.left
                        -- TODO: Here we probably have to argue something like this:
                        --       * If otherCell does not contain last n, we can use the preimage of otherCell to show
                        --         uniqueness
                        --       * If otherCell does contain last n, it's pre image must be the targetCell, ...
                        have := otherCell.mem_or_not_mem (Fin.last n)
                        cases this with
                          | inl h_last_mem_otherCell =>
                            cases h_targetCell.left with
                              | inl targetCell_eq_empty =>
                                sorry
                              | inr targetCell_mem_partition =>
                                -- TODO: These two should be lemmas
                                --have last_mem_targetCell' : Fin.last n ∈ targetCell.insertLast := by
                                --  simp [Cell.insertLast, Set.insert]
                                --have targetCell'_mem_insertLastAt : targetCell.insertLast ∈ partition.insertLastAt targetCell := by
                                --  simp [Split.insertLastAt, Set.insert]
                                --have := Split.insertLastAt_unique_cell_last_mem partition targetCell
                                --have : otherCell = targetCell.insertLast := by
                                --  sorry
                                -- TODO: Argue like this:
                                --          * Fin.last n ∈ otherCell → otherCell = targetCell.insertLast
                                --          * x ∈ otherCell → Fin.castPred x h_ne ∈ targetCell
                                --          * cell' = targetCell
                                have cell'_eq_targetCell : cell' = targetCell := by
                                  have otherCell_eq_insertLast_targetCell : otherCell = targetCell.insertLast := by
                                    have p_otherCell := And.intro otherCell_mem_split' h_last_mem_otherCell
                                    have p_insertLast_targetCell : targetCell.insertLast ∈ partition.insertLastAt targetCell ∧ Fin.last n ∈ targetCell.insertLast := by
                                      constructor
                                      · simp [Split.insertLastAt, Set.insert]
                                      · simp [Cell.insertLast, Set.insert]
                                    have := Split.insertLastAt_unique_cell_last_mem partition targetCell
                                    exact ExistsUnique.unique this p_otherCell p_insertLast_targetCell
                                  have castPred_x_mem_targetCell : x.castPred h_ne ∈ targetCell := by
                                    have : x ∈ targetCell.insertLast := by
                                      rw [otherCell_eq_insertLast_targetCell] at h_otherCell
                                      exact h_otherCell.right
                                    simp [Cell.insertLast, Set.insert] at this
                                    have := or_iff_not_imp_left.mp this h_ne
                                    exact Cell.castPred_mem_of_mem_castSucc_of_ne_last this _
                                  exact (h_cell'.right targetCell targetCell_mem_partition castPred_x_mem_targetCell).symm
                                contradiction
                                -- TODO: show that otherCell = targetCell
                                --have : otherCell = targetCell := by
                                --  sorry
                          | inr h_last_not_mem_otherCell =>
                            --have := h_cell'.right (otherCell.castPred sorry) h_otherCell.left
                            sorry
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
