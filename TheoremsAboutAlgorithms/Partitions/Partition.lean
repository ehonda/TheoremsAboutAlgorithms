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

-- WIP (II)

-- TODO: This name is probably not quite right
theorem isPartition_of_mem_insertLast'_of_isPartition
    -- We use split : Split (n + 1) here because that's the form we need it in further down below
    {n : ℕ}
    {partition : Split n}
    {split : Split (n + 1)}
    -- TODO: Can we get rid of `succ_n_pos` here? It's just trivial
    {succ_n_pos : n + 1 > 0}
    (partition_mem_partitions : partition ∈ ℙ n)
    (split_mem_insertLast'_partition : split ∈ partition.insertLast' succ_n_pos)
  : split.IsPartition := by
    -- TODO: This is our rewrite of `insertLast'_produces_partitions` where we plan to use `insertLastAt_bijOn` to prove
    --       the covering of all x.
    -- Terminology:
    --   * partition₀ := partition.insert ∅
    --   * partition' := partition.insertLastAt targetCell
    simp [Split.insertLast', Split.insertLast] at split_mem_insertLast'_partition
    obtain ⟨targetCell, targetCell_mem_partition₀, cast_partition'_eq_split⟩ := split_mem_insertLast'_partition
    constructor
    · let partition' := partition.insertLastAt targetCell
      rw [← cast_partition'_eq_split]
      apply (Split.cast_empty_not_mem_iff _ partition').mpr
      exact Split.insertLastAt_empty_not_mem_of_empty_not_mem partition targetCell partition_mem_partitions.left
    · intro x
      simp
      cases Decidable.eq_or_ne x (Fin.last _) with
        | inl x_eq_last =>
          -- TODO: Pretty much the same as in our first attempt
          sorry
        | inr x_ne_last =>
          -- TODO: Plan
          --      1. Use `x.castPred` to get an x covered by unique cell in partition
          --      2. Use `f` from `WIP (I)` to get the cell in partition' that covers x
          --      3. Show that this cell is unique via assuming `otherCell` exists, and going backwards using `g` from
          --         `WIP (I)`
          obtain ⟨cellₚ, cellₚ_def, cellₚ_unique⟩ := partition_mem_partitions.right (x.castPred x_ne_last)
          simp at cellₚ_def cellₚ_unique
          let cell := Split.f' partition targetCell cellₚ
          apply ExistsUnique.intro cell
          · sorry
          · intro otherCell otherCell_mem_partition'
            let otherCellₚ := Split.g' partition targetCell otherCell
            apply (Split.bijective_g' partition targetCell).left
            have cellₚ_eq_g'_cell : cellₚ = Split.g' partition targetCell cell := by
              sorry
            have otherCellₚ_eq_cellₚ : otherCellₚ = cellₚ := by
              sorry
            rw [←cellₚ_eq_g'_cell]
            exact otherCellₚ_eq_cellₚ

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
                    -- Here we have that x ∈ cell' and cell' = targetCell
                    | inl h_eq_targetCell =>
                      simp [Set.insert] at h_targetCell
                      cases h_targetCell.left with
                      -- Case targetCell = ∅
                        | inl h_empty =>
                          have := Set.not_mem_empty (x.castPred h_ne)
                          have : x.castPred h_ne ∈ ∅ := by
                            rw [h_eq_targetCell, h_empty] at h_cell'
                            exact h_cell'.left.right
                          contradiction
                        -- Case targetCell ∈ partition
                        | inr h_targetCell_mem_partition =>
                          -- We want to show that cell'.insertLast is the unique cell that covers x and to that end we
                          -- apply ExistsUnique.intro
                          apply ExistsUnique.intro (Cell.insertLast cell')
                          -- We show that cell'.insertLast is in split and that x is in it
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
                          -- We show that cell'.insertLast is unique by assuming that there is another cell that covers
                          -- x and showing that it must be cell'.insertLast
                          · intro otherCell h_otherCell
                            have otherCell_mem_split' : otherCell ∈ Split.insertLastAt partition targetCell := by
                              rw [← h_targetCell.right] at h_otherCell
                              apply (Split.cast_mem_iff (partition.insertLastAt targetCell) otherCell).mp
                              exact h_otherCell.left
                            -- TODO: This is very similar to what we should below, except here we have cell'.insertLast
                            --       instead of cell'.castSucc. How can we leverage that?
                            have := otherCell.mem_or_not_mem (Fin.last n)
                            cases this with
                              | inl last_mem_otherCell =>
                                -- TODO: This is duplicate code, extract it into a lemma
                                have otherCell_eq_insertLast_targetCell : otherCell = targetCell.insertLast := by
                                  have p_otherCell := And.intro otherCell_mem_split' last_mem_otherCell
                                  have p_insertLast_targetCell : targetCell.insertLast ∈ partition.insertLastAt targetCell ∧ Fin.last n ∈ targetCell.insertLast := by
                                    constructor
                                    · simp [Split.insertLastAt, Set.insert]
                                    · simp [Cell.insertLast, Set.insert]
                                  have := Split.insertLastAt_unique_cell_last_mem partition targetCell
                                  exact ExistsUnique.unique this p_otherCell p_insertLast_targetCell
                                rw [h_eq_targetCell]
                                exact otherCell_eq_insertLast_targetCell
                              | inr last_not_mem_otherCell =>
                                -- (I)
                                -- TODO: Plan:
                                --        * We probably castPred over otherCell here?
                                --        * Then we get otherCell' which contains x.castPred
                                --        * We also know otherCell' ∈ partition (How?)
                                --        * We can then show that otherCell' = cell' = targetCell
                                --        * What next? How do we get to a contradiction?
                                have mem_otherCell_ne_last : ∀ x ∈ otherCell, x ≠ Fin.last n := by
                                  intro y h_y
                                  sorry
                                have x_mem_otherCell' : x.castPred h_ne ∈ otherCell.castPred mem_otherCell_ne_last := by
                                  simp [Cell.castPred, Set.range_restrict, Cell.restrictFinCastPred, Set.restrict]
                                  exists x
                                  exists h_otherCell.right
                                have otherCell'_mem_partition : otherCell.castPred mem_otherCell_ne_last ∈ partition := by
                                  sorry
                                have targetCell_eq_otherCell' : targetCell = otherCell.castPred mem_otherCell_ne_last := by
                                  have : cell' = otherCell.castPred mem_otherCell_ne_last :=
                                    (h_cell'.right (otherCell.castPred mem_otherCell_ne_last) otherCell'_mem_partition x_mem_otherCell').symm
                                  rw [←this, h_eq_targetCell]
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
                            -- TODO: Extract lemma for this `otherCell = targetCell.insertLast`
                            have otherCell_eq_insertLast_targetCell : otherCell = targetCell.insertLast := by
                              have p_otherCell := And.intro otherCell_mem_split' h_last_mem_otherCell
                              have p_insertLast_targetCell : targetCell.insertLast ∈ partition.insertLastAt targetCell ∧ Fin.last n ∈ targetCell.insertLast := by
                                constructor
                                · simp [Split.insertLastAt, Set.insert]
                                · simp [Cell.insertLast, Set.insert]
                              have := Split.insertLastAt_unique_cell_last_mem partition targetCell
                              exact ExistsUnique.unique this p_otherCell p_insertLast_targetCell
                            cases h_targetCell.left with
                              | inl targetCell_eq_empty =>
                                have : x = Fin.last n := by
                                  rw [otherCell_eq_insertLast_targetCell, targetCell_eq_empty] at h_otherCell
                                  simp [Cell.insertLast, Set.insert] at h_otherCell
                                  have : x ∉ Cell.castSucc ∅ := by simp [Cell.castSucc]
                                  exact or_iff_not_imp_right.mp h_otherCell.right this
                                contradiction
                              | inr targetCell_mem_partition =>
                                have cell'_eq_targetCell : cell' = targetCell := by
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
                            -- TODO: See how we do it in (I) and argue similarly here
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
