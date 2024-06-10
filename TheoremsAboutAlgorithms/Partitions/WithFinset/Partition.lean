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
    · intro empty_mem_split
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
          exact empty_mem_partition
    · intro x
      cases Decidable.eq_or_ne x (Fin.last _) with
        | inl x_eq_last =>
          simp [Split.insertLast, Finset.toSetEmbedding] at *
          -- TODO: We use this in a sibling goal as well, move further up so we only have to do this once
          obtain ⟨targetCell, _, insertLastAt_partition_targetCell_eq_split⟩
            := split_mem_insertLast_partition
          -- TODO: We should have a proof for this in `UpwardDownward`, use it here
          exists ⟨Cell.insertLast targetCell, by simp [insertLastAt_partition_targetCell_eq_split.symm, Split.insertLastAt]⟩
          simp
          constructor
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
          obtain ⟨cell', x'_mem_cell', cell'_unique⟩ := partition_mem_partitions.right x'
          simp at x'_mem_cell'
          -- TODO: We use this in a sibling goal as well, move further up so we only have to do this once
          obtain ⟨targetCell, targetCell_mem_insertEmpty_partition, insertLastAt_partition_targetCell_eq_split⟩
            := split_mem_insertLast_partition
          -- We `subst split` here so we don't have to do
          --
          --    `insertLastAt_partition_targetCell_eq_split ▸ Split.upward cell'`
          --
          -- which is hard to get rid of (the `▸`).
          subst split
          -- exists insertLastAt_partition_targetCell_eq_split ▸ Split.upward cell'
          exists Split.upward cell'
          simp [Split.upward]
          constructor
          · split
            case _ cell'_eq_targetCell =>
              simp [CoeDep.coe, Cell.insertLast]
              right
              exact Cell.mem_castSucc_of_ne_last_of_castPred_mem x_ne_last x'_mem_cell'
            case _ cell'_ne_targetCell =>
              simp [CoeDep.coe, Cell.castSucc]
              exists Fin.castPred x x_ne_last
          · intro otherCell otherCell_mem_split x_mem_otherCell
            split
            case _ cell'_eq_targetCell =>
              simp [CoeDep.coe]
              simp [Split.insertEmpty] at targetCell_mem_insertEmpty_partition
              cases targetCell_mem_insertEmpty_partition with
                | inl targetCell_eq_empty =>
                  subst targetCell
                  absurd cell'.property
                  rw [targetCell_eq_empty]
                  exact partition_mem_partitions.left
                | inr targetCell_mem_partition =>
                  set otherCell' := Split.downward
                      partition
                      ⟨targetCell, targetCell_mem_partition⟩
                      ⟨otherCell, otherCell_mem_split⟩
                    with otherCell'_def
                  unfold Split.downward at otherCell'_def
                  split at otherCell'_def
                  case _ => subst targetCell; assumption
                  case _ otherCell'_ne_targetCell =>
                    -- TODO: This whole prove is very messy, there should be an easier way
                    simp at otherCell'_ne_targetCell
                    simp [Split.insertLastAt, otherCell'_ne_targetCell, Split.castSucc, Cell.castSuccEmbedding] at otherCell_mem_split
                    obtain ⟨otherCell_ne_castSucc_targetCell, otherCell'', otherCell''_mem_partition, castSucc_otherCell''_eq_otherCell⟩
                      := otherCell_mem_split
                    have otherCell''_eq_cell' : ⟨otherCell'', otherCell''_mem_partition⟩ = cell' := by
                      have x'_mem_otherCell'' : x' ∈ otherCell'' := by
                        rw [← castSucc_otherCell''_eq_otherCell] at x_mem_otherCell
                        exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                      subst targetCell
                      apply cell'_unique ⟨otherCell'', otherCell''_mem_partition⟩
                      exact x'_mem_otherCell''
                    have otherCell''_eq_targetCell : otherCell'' = targetCell := by
                      subst targetCell
                      exact Subtype.val_inj.mpr otherCell''_eq_cell'
                    -- TODO: There has to be a more direct way to get the contradicition here
                    absurd castSucc_otherCell''_eq_otherCell
                    rw [otherCell''_eq_targetCell]
                    intro castSucc_targetCell_eq_otherCell
                    rw [castSucc_targetCell_eq_otherCell] at otherCell_ne_castSucc_targetCell
                    contradiction
            case _ cell'_ne_targetCell =>
              simp [Split.insertLastAt] at otherCell_mem_split
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
                      have : ⟨targetCell, targetCell_mem_partition⟩ = cell' := by
                        apply cell'_unique ⟨targetCell, targetCell_mem_partition⟩
                        simp
                        rw [otherCell_eq_insertLast_targetCell] at x_mem_otherCell
                        simp [x_ne_last] at x_mem_otherCell
                        exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                      exact Subtype.val_inj.mpr this.symm
                | inr otherCell_mem_partition =>
                  simp [Split.castSucc, Cell.castSuccEmbedding] at otherCell_mem_partition
                  obtain ⟨_, otherCell', otherCell'_mem_partition, castSucc_otherCell'_eq_otherCell⟩
                    := otherCell_mem_partition
                  -- TODO: We use this pattern in at least three sub goals, refactor into a lemma
                  have : otherCell' = cell' := by
                    have : ⟨otherCell', otherCell'_mem_partition⟩ = cell' := by
                      apply cell'_unique ⟨otherCell', otherCell'_mem_partition⟩
                      simp
                      rw [← castSucc_otherCell'_eq_otherCell] at x_mem_otherCell
                      exact Cell.castPred_mem_of_mem_castSucc_of_ne_last x_mem_otherCell x_ne_last
                    exact Subtype.val_inj.mpr this
                  subst otherCell'
                  simp [CoeDep.coe]
                  exact castSucc_otherCell'_eq_otherCell.symm

-- m : ℕ
-- partition : Split (Nat.succ m)
-- partition_mem_partitions : partition ∈ ℙ (Nat.succ m)
-- ⊢ ∃ i, partition ∈ ⋃ (_ : i ∈ ℙ m), Split.insertLast i

-- TODO: Naming
theorem helper
    {n : ℕ}
    {partition : Split (n + 1)}
    {partition_mem_partitions : partition ∈ ℙ (n + 1)}
  :  ∃ partition', partition ∈ ⋃ (_ : partition' ∈ ℙ n), Split.insertLast partition' := by
    -- TODO: Plan
    --      * We need the fact that there exists a unique cell containing last for any partition
    --      * We chose this cell as the target cell (with last removed)
    --      * We then map `Split.downwardEmbedding` over the partition
    -- let cellContainingLast := partition_mem_partitions.right (Fin.last _)
    obtain ⟨targetCell', last_mem_targetCell', targetCell'_unique⟩ := partition_mem_partitions.right (Fin.last _)
    -- TODO: Horrible naming, find a better name for `targetCell''` and `partition''`
    --       Alternatively, find a way to factor these out, do the dirty work in a helper and just return what we need
    --       here. These are just intermediary objects that we don't need subsequently in this proof.
    set targetCell'' := targetCell'.val.erase (Fin.last _) with targetCell''_def
    have castPredPrecondition_targetCell'' : Cell.CastPredPrecondition targetCell'' := by
      intro x x_mem_targetCell'' x_eq_last
      absurd Finset.not_mem_erase (Fin.last _) targetCell'.val
      rw [x_eq_last, targetCell''_def] at x_mem_targetCell''
      assumption
    set targetCell := Cell.castPred targetCell'' castPredPrecondition_targetCell'' with targetCell_def
    set partition'' := partition.erase targetCell' with partition''_def
    have castPredPrecondition_partition'' : Split.CastPredPrecondition partition'' := by
      intro cell cell_mem_partition'' x x_mem_cell x_eq_last
      simp [partition''_def] at cell_mem_partition''
      obtain ⟨cell_ne_targetCell', cell_mem_partition⟩ := cell_mem_partition''
      have subtype_cell_eq_targetCell' : ⟨cell, cell_mem_partition⟩ = targetCell' := by
        apply targetCell'_unique ⟨cell, cell_mem_partition⟩
        rw [x_eq_last] at x_mem_cell
        assumption
      have := Subtype.val_inj.mpr subtype_cell_eq_targetCell'
      contradiction
    -- We can only insert `targetCell` if it is nonempty, otherwise the result will not be a partition. If it is empty
    -- we get it via `partition.insertLast` which uses `partition.insertEmpty`.
    set partition' :=
      if ∅ = targetCell
      then (Split.castPred partition'' castPredPrecondition_partition'')
      else insert targetCell (Split.castPred partition'' castPredPrecondition_partition'')
      with partition'_def
    exists partition'
    simp
    constructor
    · constructor
      · split
        case _ empty_eq_castPred_targetCell'' =>
          -- TODO: This is the exact same proof as the `inr` case below, factor out
          intro empty_mem_castPred_partition''
          have : ∅ ∈ (Split.castPred partition'' castPredPrecondition_partition'').castSucc := by
            rw [Split.castSucc_castPred_eq, partition''_def]
            apply Split.empty_mem_castPred_iff_empty_mem.mp empty_mem_castPred_partition''
          have empty_mem_partition : ∅ ∈ partition := by
            rw [Split.castSucc_castPred_eq] at this
            simp [partition''_def] at this
            exact this.right
          absurd partition_mem_partitions.left
          exact empty_mem_partition
        case _ empty_ne_castPred_targetCell'' =>
          simp
          intro empty_eq_castPred_targetCell''_or_empty_mem_castPred_partition''
          cases empty_eq_castPred_targetCell''_or_empty_mem_castPred_partition'' with
            | inl _ => contradiction
            | inr empty_mem_castPred_partition'' =>
              have : ∅ ∈ (Split.castPred partition'' castPredPrecondition_partition'').castSucc := by
                rw [Split.castSucc_castPred_eq, partition''_def]
                apply Split.empty_mem_castPred_iff_empty_mem.mp empty_mem_castPred_partition''
              have empty_mem_partition : ∅ ∈ partition := by
                rw [Split.castSucc_castPred_eq] at this
                simp [partition''_def] at this
                exact this.right
              absurd partition_mem_partitions.left
              exact empty_mem_partition
      · intro x
        set x' := x.castSucc with x'_def
        have := partition_mem_partitions.right x'
        obtain ⟨cell', castSucc_x_mem_cell', cell'_unique⟩ := this
        cases Decidable.eq_or_ne cell' targetCell' with
          | inl cell'_eq_targetCell' =>
            -- This is valid but temoprarily deactivated to reduce lag while proving the rest
            sorry
            -- have targetCell_mem_partition : targetCell ∈ partition' := by
            --   simp [partition'_def]
            --   split
            --   case _ empty_eq_targetCell =>
            --     have targetCell'_val_eq_singleton_last : targetCell'.val = {Fin.last _} := by
            --       rw [targetCell_def] at empty_eq_targetCell
            --       simp [targetCell''_def] at empty_eq_targetCell
            --       apply (Cell.empty_eq_castPred_iff_empty_eq).mp at empty_eq_targetCell
            --       symm at empty_eq_targetCell
            --       apply (Finset.erase_eq_empty_iff targetCell'.val (Fin.last _)).mp at empty_eq_targetCell
            --       cases empty_eq_targetCell with
            --         | inl targetCell'_val_eq_empty =>
            --           rw [targetCell'_val_eq_empty] at last_mem_targetCell'
            --           contradiction
            --         | inr targetCell'_val_eq_singleton_last =>
            --           exact targetCell'_val_eq_singleton_last
            --     have x'_eq_last : x' = Fin.last _ := by
            --       subst targetCell'
            --       rw [targetCell'_val_eq_singleton_last] at castSucc_x_mem_cell'
            --       apply Finset.eq_of_mem_singleton
            --       assumption
            --     have := x.castSucc_ne_last
            --     contradiction
            --   case _ targetCell_ne_empty => simp
            -- exists ⟨targetCell, targetCell_mem_partition⟩
            -- simp
            -- constructor
            -- · apply (Cell.mem_castPred_iff_castSucc_mem_of_castPredPrecondition _).mpr
            --   subst cell'
            --   have x'_mem_targetCell'' : x' ∈ targetCell'' := by
            --     simp [targetCell''_def]
            --     constructor
            --     · exact x.castSucc_ne_last
            --     · assumption
            --   assumption
            -- · intro otherCell otherCell_mem_partition' x_mem_otherCell
            --   -- TODO: This is a lot of inlined work, we should be able to define functions that give us the key
            --   --       components and modularize the proof that way
            --   cases Decidable.eq_or_ne otherCell targetCell with
            --     | inl otherCell_eq_targetCell =>
            --       subst otherCell
            --       simp [targetCell''_def]
            --     | inr otherCell_ne_targetCell =>
            --       subst cell'
            --       set otherCell' := otherCell.castSucc with otherCell'_def
            --       have x'_mem_otherCell' : x' ∈ otherCell' := by
            --         simp [otherCell'_def, x'_def, Cell.castSucc]
            --         exists x
            --       have otherCell'_mem_partition : otherCell' ∈ partition := by
            --         simp [otherCell'_def]
            --         split at otherCell_mem_partition'
            --         case _ empty_eq_targetCell =>
            --           simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict] at otherCell_mem_partition'
            --           obtain ⟨otherCell'', ⟨otherCell''_ne_targetCell', otherCell''_mem_partition⟩, castPred_otherCell''_eq_otherCell⟩
            --             := otherCell_mem_partition'
            --           subst otherCell
            --           simp [Cell.castSucc_castPred_eq]
            --           assumption
            --         case _ otherCell'_ne_targetCell' =>
            --           simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict] at otherCell_mem_partition'
            --           cases otherCell_mem_partition' with
            --             | inl otherCell_eq_targetCell => contradiction
            --             | inr exists_castPred_eq_otherCell =>
            --               obtain ⟨otherCell'', ⟨otherCell''_ne_targetCell', otherCell''_mem_partition⟩, castPred_otherCell''_eq_otherCell⟩
            --                 := exists_castPred_eq_otherCell
            --               subst otherCell
            --               simp [Cell.castSucc_castPred_eq]
            --               assumption
            --       have subtype_otherCell'_eq_targetCell' : ⟨otherCell', otherCell'_mem_partition⟩ = targetCell' := by
            --         apply cell'_unique ⟨otherCell', _⟩
            --         simp
            --         exact x'_mem_otherCell'
            --       have otherCell'_eq_targetCell'_val : otherCell' = targetCell'
            --         := Subtype.val_inj.mpr subtype_otherCell'_eq_targetCell'
            --       set otherCell'' := otherCell.castSucc.erase (Fin.last _) with otherCell''_def
            --       have : otherCell = targetCell := by
            --         subst targetCell'
            --         simp [targetCell_def]
            --         have otherCell''_eq_castSucc_otherCell : otherCell'' = otherCell.castSucc := by
            --           simp [otherCell''_def, Cell.castSucc]
            --           intro x _
            --           exact x.castSucc_ne_last
            --         -- TODO: There should be a way easier way since we know that `otherCell'' = Cell.castSucc otherCell`
            --         --       and therefore Cell.castPred (Finset.erase (Cell.castSucc otherCell) (Fin.last n)) castPredPrecondition_targetCell''
            --         --       and therefore `otherCell''.castPred _ = otherCell.castSucc.castPred _ = otherCell`,
            --         --       but its tough to `rw` / `simp` / `subst` because of the dependent
            --         ---      `Cell.castPredPrecondition`
            --         -- simp [Cell.castPred]
            --         -- unfold Cell.restrictFinCastPred
            --         -- simp [Subtype.restrict]
            --         ext f
            --         constructor
            --         · intro f_mem_otherCell
            --           apply (Cell.mem_castPred_iff_castSucc_mem_of_castPredPrecondition _).mpr
            --           simp [otherCell''_def]
            --           constructor
            --           · exact f.castSucc_ne_last
            --           · simp [Cell.castSucc]; exists f
            --         · intro f_mem_otherCell''
            --           simp [Cell.castPred, Cell.restrictFinCastPred, Subtype.restrict, Cell.castSucc]
            --             at f_mem_otherCell''
            --           obtain ⟨f', ⟨f'_ne_last, f'', f''_mem_otherCell, castSucc_f''_eq_f'⟩, castPred_f'_eq_f⟩
            --             := f_mem_otherCell''
            --           subst f f'
            --           simp
            --           assumption
            --       contradiction
          | inr cell'_ne_targetCell' =>
            -- This is valid but temoprarily deactivated to reduce lag while proving the rest
            sorry
            -- have castPredPrecondition_cell' : Cell.CastPredPrecondition (cell' : Cell (n + 1)) := by
            --   intro x x_mem_cell' x_eq_last
            --   have cell'_eq_targetCell' : cell' = targetCell' := by
            --     apply targetCell'_unique cell'
            --     rw [x_eq_last] at x_mem_cell'
            --     assumption
            --   contradiction
            -- set cell := Cell.castPred cell' castPredPrecondition_cell' with cell_def
            -- have cell_mem_partition' : cell ∈ partition' := by
            --   simp [partition'_def]
            --   split
            --   case _ empty_eq_targetCell =>
            --     simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict]
            --     exists cell'
            --     constructor
            --     · rfl
            --     · constructor
            --       -- TODO: There's for sure an easier way for this sub goal
            --       · intro; apply cell'_ne_targetCell'; apply Subtype.val_inj.mp; assumption
            --       · exact cell'.property
            --   case _ empty_ne_targetCell =>
            --     simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict]
            --     right
            --     -- TODO: Exact duplication of the case above, refactor!
            --     exists cell'
            --     constructor
            --     · rfl
            --     · constructor
            --       -- TODO: There's for sure an easier way for this sub goal
            --       · intro; apply cell'_ne_targetCell'; apply Subtype.val_inj.mp; assumption
            --       · exact cell'.property
            -- exists ⟨cell, cell_mem_partition'⟩
            -- simp
            -- constructor
            -- · apply (Cell.mem_castPred_iff_castSucc_mem_of_castPredPrecondition _).mpr
            --   simp [x'_def] at castSucc_x_mem_cell'
            --   assumption
            -- · intro otherCell otherCell_mem_partition' x_mem_otherCell
            --   -- TODO: Set makes stuff hard to work with, which is why we inline `otherCell.castSucc = otherCell'` here.
            --   --       Maybe we could use it without issue though.
            --   -- set otherCell' := otherCell.castSucc with otherCell'_def
            --   have otherCell'_mem_partition : otherCell.castSucc ∈ partition := by
            --     split at otherCell_mem_partition'
            --     case _ empty_eq_targetCell =>
            --       simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict] at otherCell_mem_partition'
            --       obtain ⟨otherCell'', ⟨otherCell''_ne_targetCell', otherCell''_mem_partition⟩, castPred_otherCell''_eq_otherCell⟩
            --         := otherCell_mem_partition'
            --       subst otherCell
            --       simp [Cell.castSucc_castPred_eq]
            --       assumption
            --     case _ empty_ne_targetCell =>
            --       simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict] at otherCell_mem_partition'
            --       cases otherCell_mem_partition' with
            --         | inl otherCell_eq_targetCell =>
            --           have x'_mem_targetCell'_val : x' ∈ targetCell'.val := by
            --             subst otherCell
            --             simp [Cell.castPred, Cell.restrictFinCastPred, Subtype.restrict] at x_mem_otherCell
            --             obtain ⟨x'', ⟨x''_ne_last, x''_mem_targetCell'_val⟩, castPred_x''_eq_x⟩
            --               := x_mem_otherCell
            --             subst x
            --             simp [x'_def]
            --             assumption
            --           have targetCell'_eq_cell' : targetCell' = cell' := by
            --             apply cell'_unique targetCell'
            --             assumption
            --           symm at targetCell'_eq_cell'
            --           contradiction
            --         | inr exists_castPred_eq_otherCell =>
            --           -- TODO: Again lots of repetition, refactor!
            --           obtain ⟨otherCell'', ⟨otherCell''_ne_targetCell', otherCell''_mem_partition⟩, castPred_otherCell''_eq_otherCell⟩
            --             := exists_castPred_eq_otherCell
            --           subst otherCell
            --           simp [Cell.castSucc_castPred_eq]
            --           assumption
            --   have x'_mem_otherCell' : x' ∈ otherCell.castSucc := by
            --     simp [x'_def, Cell.castSucc]
            --     exists x
            --   have subtype_otherCell'_eq_cell' : ⟨otherCell.castSucc, otherCell'_mem_partition⟩ = cell' := by
            --     apply cell'_unique ⟨otherCell.castSucc, _⟩
            --     assumption
            --   have otherCell'_eq_cell' : otherCell.castSucc = cell' := Subtype.val_inj.mpr subtype_otherCell'_eq_cell'
            --   subst cell'
            --   simp [Cell.castPred_castSucc_eq]
    · simp [Split.insertLast]
      exists targetCell
      constructor
      · split
        case _ targetCell_eq_empty =>
          simp [targetCell_def, targetCell''_def, Split.insertEmpty]
          left
          symm
          assumption
        case _ targetCell_ne_empty =>
          simp [targetCell_def, targetCell''_def, Split.insertEmpty]
      · split
        case _ targetCell_eq_empty =>
          ext cell
          constructor
          · intro cell_mem_partition'
            simp [Split.insertLastAt] at cell_mem_partition'
            cases cell_mem_partition' with
              | inl cell_eq_targetCell =>
                have cell_eq_targetCell' : cell = targetCell' := by
                  rw [cell_eq_targetCell]
                  simp [Cell.insertLast]
                  ext f
                  constructor
                  · intro f_mem_insert_last_castSucc_targetCell
                    simp at f_mem_insert_last_castSucc_targetCell
                    cases f_mem_insert_last_castSucc_targetCell with
                      | inl f_eq_last =>
                        subst f
                        assumption
                      | inr f_mem_castSucc_targetCell =>
                        simp [Cell.castSucc_castPred_eq] at f_mem_castSucc_targetCell
                        exact f_mem_castSucc_targetCell.right
                  · intro f_mem_targetCell'
                    simp
                    cases Decidable.eq_or_ne f (Fin.last _) with
                      | inl f_eq_last => left; assumption
                      | inr f_ne_last =>
                        simp [Cell.castSucc_castPred_eq]
                        right
                        constructor
                        · assumption
                        · assumption
                rw [cell_eq_targetCell']
                exact targetCell'.property
              | inr cell_mem_partition''' =>
                simp [Split.castSucc, Cell.castSuccEmbedding] at cell_mem_partition'''
                obtain ⟨cell_ne_castSucc_targetCell'', cell', cell'_mem_castPred_partition'', castSucc_cell'_eq_cell⟩
                  := cell_mem_partition'''
                subst cell
                simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict] at cell'_mem_castPred_partition''
                obtain ⟨cell'', ⟨cell''_ne_targetCell'', cell''_mem_partition''⟩, castPred_cell''_eq_cell'⟩
                  := cell'_mem_castPred_partition''
                subst cell'
                simp [Cell.castSucc_castPred_eq]
                assumption
          · intro cell_mem_partition
            simp [Split.insertLastAt]
            cases Decidable.eq_or_ne cell targetCell' with
              | inl cell_eq_targetCell =>
                subst cell
                left
                simp [Cell.insertLast, Cell.castSucc_castPred_eq]
                rw [Finset.insert_erase last_mem_targetCell']
              | inr cell_ne_targetCell =>
                right
                simp [Split.castSucc, Cell.castSuccEmbedding]
                constructor
                · intro cell_eq_castSucc_castPred_targetCell
                  have cell_eq_targetCell : cell = ↑targetCell' := by
                    simp [Cell.castSucc_castPred_eq] at cell_eq_castSucc_castPred_targetCell
                    cases Decidable.eq_or_ne targetCell'.val {Fin.last _} with
                      | inl targetCell'_val_eq_singleton_last =>
                        simp [targetCell'_val_eq_singleton_last] at cell_eq_castSucc_castPred_targetCell
                        absurd partition_mem_partitions.left
                        rw [cell_eq_castSucc_castPred_targetCell] at cell_mem_partition
                        assumption
                      | inr targetCell'_val_ne_singleton_last =>
                        have exists_mem_targetCell'_ne_last : ∃ x, x ∈ targetCell'.val ∧ x ≠ Fin.last _ := by
                          have targetCell'_nontrivial : targetCell'.val.Nontrivial := by
                            apply (Finset.nontrivial_iff_ne_singleton last_mem_targetCell').mpr
                            assumption
                          have nontrivial_subtype_targetCell' : Nontrivial { x // x ∈ targetCell'.val } := by
                            cases subsingleton_or_nontrivial { x // x ∈ targetCell'.val } with
                              | inl subsingleton_subtype_targetCell' =>
                                obtain ⟨x, x_mem_targetCell', y, y_mem_targetCell', x_ne_y⟩ := targetCell'_nontrivial
                                absurd x_ne_y
                                have := subsingleton_subtype_targetCell'.allEq ⟨x, x_mem_targetCell'⟩ ⟨y, y_mem_targetCell'⟩
                                exact Subtype.val_inj.mpr this
                              | inr nontrivial_subtype_targetCell' =>
                                assumption
                          have exists_subtype_targetCell'_ne_last : ∃ (x : targetCell'.val), (x : Fin (n + 1)) ≠ Fin.last _ := by
                            have := (nontrivial_iff_exists_ne (⟨Fin.last _, last_mem_targetCell'⟩ : Subtype (· ∈ targetCell'.val))).mp nontrivial_subtype_targetCell'
                            obtain ⟨x, x_ne_last⟩ := this
                            exists x
                            intro x_val_eq_last
                            have x_eq_last : x = ⟨Fin.last _, last_mem_targetCell'⟩ := by
                              apply Subtype.eq
                              assumption
                            contradiction
                          obtain ⟨x, x_ne_last⟩ := exists_subtype_targetCell'_ne_last
                          exists x
                          constructor
                          · exact x.property
                          · assumption
                        obtain ⟨x, x_mem_targetCell', x_ne_last⟩ := exists_mem_targetCell'_ne_last
                        -- targetCell'_unique : ∀ (y : { x // x ∈ partition }), (fun cell ↦ Fin.last n ∈ ↑cell) y → y = targetCell'
                        have targetCell'_unique_x : ∀ (y : { x // x ∈ partition }), (fun cell ↦ x ∈ (cell : Cell (n + 1))) y → y = targetCell' := by
                          obtain ⟨cell', x_mem_cell', cell'_unique⟩ := partition_mem_partitions.right x
                          have cell'_eq_targetCell' : targetCell' = cell' := by
                            apply cell'_unique targetCell'
                            assumption
                          subst cell'
                          assumption
                        have x_mem_cell : x ∈ cell := by
                          rw [cell_eq_castSucc_castPred_targetCell]
                          simp
                          constructor
                          · assumption
                          · assumption
                        -- TODO: We have this pattern everywhere, it should be a lemma
                        have cell_eq_targetCell' : cell = targetCell' := by
                          have subtype_cell_eq_targetCell' : ⟨cell, cell_mem_partition⟩ = targetCell' := by
                            apply targetCell'_unique_x ⟨cell, cell_mem_partition⟩
                            assumption
                          exact Subtype.val_inj.mpr subtype_cell_eq_targetCell'
                        contradiction
                  contradiction
                · have castPredPrecondition_cell : cell.CastPredPrecondition := by
                    intro x x_mem_cell x_eq_last
                    have cell_eq_targetCell' : cell = targetCell' := by
                      have subtype_cell_eq_targetCell' : ⟨cell, cell_mem_partition⟩ = targetCell' := by
                        apply targetCell'_unique ⟨cell, cell_mem_partition⟩
                        simp
                        rw [x_eq_last] at x_mem_cell
                        assumption
                      exact Subtype.val_inj.mpr subtype_cell_eq_targetCell'
                    contradiction
                  exists cell.castPred castPredPrecondition_cell
                  constructor
                  · simp [Split.castPred, Split.restrictCellCastPred, Subtype.restrict]
                    exists cell
                    constructor
                    · rfl
                    · constructor
                      · assumption
                      · assumption
                  · simp [Cell.castSucc_castPred_eq]
        case _ targetCell_ne_empty =>
          sorry

-- Plan:
--    * Map downward on partition (:= split)
--    * Show that the result is in ℙ (n - 1)
--    * Show that we get partition ∈ split.insertLast
theorem partitions_subset_recursivePartitions (n : ℕ) : ℙ n ⊆ ℙᵣ n := by
  intro partition partition_mem_partitions
  cases n with
    | zero => simp [partitions_0] at partition_mem_partitions; exact partition_mem_partitions
    | succ m =>
      apply Set.mem_iUnion.mpr
      apply helper
      assumption

theorem recursivePartitions_subset_partitions (n : ℕ) : ℙᵣ n ⊆ ℙ n := by
  intro split split_mem_recursivePartitions
  cases n with
    | zero => simp [partitions_0, recursivePartitions] at *; exact split_mem_recursivePartitions
    | succ m =>
      -- TODO: This is a bit involved, there's probably an easier way
      obtain ⟨splits, splits_mem_insertLast_partition, split_mem_splits⟩ := split_mem_recursivePartitions
      simp at splits_mem_insertLast_partition
      obtain ⟨partition, iUnion_insertLast_partition_eq_splits⟩ := splits_mem_insertLast_partition
      rw [← iUnion_insertLast_partition_eq_splits] at split_mem_splits
      simp [Set.mem_iUnion] at split_mem_splits
      obtain ⟨partition_mem_partitions, split_mem_insertLast_partition⟩ := split_mem_splits
      exact isPartition_of_mem_insertLast_of_isPartition partition_mem_partitions split_mem_insertLast_partition

theorem partitions_eq_recursivePartitions (n : ℕ) : ℙ n = ℙᵣ n := by
  apply Set.eq_of_subset_of_subset
  · exact partitions_subset_recursivePartitions n
  · exact recursivePartitions_subset_partitions n

end Partition
