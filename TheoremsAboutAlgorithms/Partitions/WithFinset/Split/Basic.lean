import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Init.Logic
import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs
import TheoremsAboutAlgorithms.Partitions.WithFinset.Cell

namespace Split

def cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Finset.map (Cell.castEmbedding h) split

theorem empty_not_mem_cast_iff_empty_not_mem {n m : ℕ} (h : n = m) (split : Split n)
  : ∅ ∉ split.cast h ↔ ∅ ∉ split
    := by simp [cast, Cell.castEmbedding, Cell.cast]

theorem mem_cast_iff_mem {n : ℕ} (split : Split n) (cell : Cell n)
  : cell ∈ split.cast rfl ↔ cell ∈ split
    := by simp [cast, Cell.castEmbedding, Cell.cast, Fin.castEmbedding, Finset.map]

theorem cast_nonempty_iff_nonempty {n m : ℕ} (h : n = m) (split : Split n)
  : (split.cast h).Nonempty ↔ split.Nonempty := by simp [cast]

def castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Finset.map Cell.castSuccEmbedding split

theorem castSucc_injective {n : ℕ} : Function.Injective (@castSucc n)
  := Finset.map_injective ⟨Cell.castSuccEmbedding, Cell.castSucc_injective _⟩

theorem empty_mem_castSucc_iff_empty_mem {n : ℕ} (split : Split n)
  : ∅ ∈ split.castSucc ↔ ∅ ∈ split := by simp [castSucc, Cell.castSucc, Cell.castSuccEmbedding]

theorem last_not_mem_of_mem_castSucc {n : ℕ} {split : Split n} {cell : Cell (n + 1)} (h : cell ∈ split.castSucc)
  : Fin.last n ∉ cell := by
    simp [castSucc, Cell.castSucc, Cell.castSuccEmbedding] at h
    cases h with
      | intro cell_pre h_cell_pre =>
        rw [← h_cell_pre.right]
        simp
        intro x _
        exact Fin.ne_of_lt (Fin.castSucc_lt_last x)

def CastPredPrecondition {n : ℕ} (split : Split (n + 1)) := ∀ cell ∈ split, Cell.CastPredPrecondition cell

-- TODO: Can we use `Subtype.restrict` here? (And do we want to?)
def restrictCellCastPred {n : ℕ} (split : Split (n + 1)) (h : CastPredPrecondition split) (cell : split) : Cell n
  := (Set.restrict split Cell.castPred cell) (h cell cell.property)

-- n : ℕ
-- split : Split (n + 1)
-- x y : { x // x ∈ split }
-- f : Cell (n + 1) ↪ Cell n
-- ⊢ Finset (Cell (n + 1))

-- type mismatch
--   Finset.attach ↑x
-- has type
--   Finset { x_1 // x_1 ∈ ↑x } : Type
-- but is expected to have type
--   Finset (Cell (n + 1)) : Type

-- instance : CoeSort (Split n) (Set (Cell n)) := ⟨λ split => split⟩
-- instance {n : ℕ} (split : Split n) (x : split) : CoeSort {f // f ∈ (x : Cell n)} (Cell n) := sorry

instance {n : ℕ} (split : Split n) (x : split) : Coe (Finset {f // f ∈ (x : Cell n)}) (Finset (Cell n)) := sorry


-- castPred_x_eq_castPred_y : Finset.map { toFun := Cell.restrictFinCastPred ↑x _, inj' := _ } (Finset.attach ↑x) =
--   Finset.map { toFun := Cell.restrictFinCastPred ↑y _, inj' := _ } (Finset.attach ↑y)
-- TODO: Where should this be?
theorem helper
    {n : ℕ}
    (split : Split (n + 1))
    (x y : split)
    (f : Cell (n + 1) ↪ Cell n)
  : Finset.map f (Finset.attach (x : Cell (n + 1)))
  -- : Finset.map f ((Finset.attach (x : Cell (n + 1))) : Finset (Cell (n + 1)))
  -- : Finset.map f ((Finset.attach (x : Cell (n + 1))) : Finset { x // x ∈ ↑y }) =
    -- (Finset.map f (Finset.attach (y : Cell (n + 1))) : Split n) → x = y := by
    Finset.map f (Finset.attach (y : Cell (n + 1))) → x = y := by
    sorry

-- TODO: Finish this proof
theorem restrictCellCastPred_injective {n : ℕ} (split : Split (n + 1)) (h : CastPredPrecondition split)
  : Function.Injective (restrictCellCastPred split h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictCellCastPred, Set.restrict, Cell.castPred] at castPred_x_eq_castPred_y
    apply Subtype.eq
    have : Cell.restrictFinCastPred (x : Cell (n + 1)) sorry = Cell.restrictFinCastPred (y : Cell (n + 1)) sorry := by
      sorry

    -- TODO: Probably use `Cell.castPred_inj` to prove this.
    --
    -- TODO: The problem here is that we can't directly apply `Finset.map_injective` as the functions we're comparing
    --       are not the same - One is `Cell.restrictFinCastPred ↑x _` and the other is `Cell.restrictFinCastPred ↑y _`.
    --       This is necessary because we can only apply `Cell.restrictFinCastPred` with it's precondition that is
    --       specific to a cell.
    --       We do have it in `Cell.restrictFinCastPred_injective` however by using `Fin.castPred_inj.mp` so there
    --       should be a way to get there, but it's without the `Finset.map` wrapping everything (which does make it a
    --       bit more complicated here - maybe we need `ext` or something?).
    --
    --       castPred_x_eq_castPred_y : Finset.map { toFun := Cell.restrictFinCastPred ↑x _, inj' := _ } (Finset.attach ↑x) =
    --                                  Finset.map { toFun := Cell.restrictFinCastPred ↑y _, inj' := _ } (Finset.attach ↑y)
    --       ⊢ x = y
    --
    --       Maybe we need an analogue to `Fin.castPred_inj := i.castPred hi = j.castPred hj ↔ i = j` (which is not
    --       classic injectivitiy since the functions are not the same, but it's the same idea).
    sorry
    -- exact Finset.map_injective
    -- exact Fin.castPred_inj.mp castPred_x_eq_castPred_y

-- TODO: Finish this
def castPred {n : ℕ} (split : Split (n + 1)) (h : CastPredPrecondition split) : Split n
  := Finset.map ⟨restrictCellCastPred split h, restrictCellCastPred_injective split h⟩ Finset.univ

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := insert (targetCell.insertLast) (split.erase targetCell |> castSucc)

-- TODO: Define notation so we can write this as split₀ for a given split
def insertEmpty {n : ℕ} (split : Split n) : Split n
  := insert ∅ split

-- TODO:
--    * Where does this belong?
--    * Is the naming right?
--    * Do we even need this?
-- theorem targetCell_eq_empty_of_singleton_last_mem_insertLastAt
--     {n : ℕ}
--     {split : Split n}
--     {targetCell : Cell n}
--     (singleton_last_mem_insertLastAt : {Fin.last _} ∈ split.insertLastAt targetCell)
--   : targetCell = ∅ := by
--     simp [insertLastAt] at singleton_last_mem_insertLastAt
--     sorry

------------------------------------------------------------------------------------------------------------------------
--                                          insertLastAt, insertLast, ...                                             --
------------------------------------------------------------------------------------------------------------------------

theorem insertLastAt_nonempty {n : ℕ} (split : Split n) (targetCell : Cell n)
  : (split.insertLastAt targetCell).Nonempty
    := by simp [insertLastAt]

def insertLast {n : ℕ} (split : Split n) : Set (Split (n + 1))
  := {split.insertLastAt cell | cell ∈ split.insertEmpty}

-- TODO: Why can't we copy this definition: https://github.com/leanprover-community/mathlib4/blob/3ab8e5819aedd7f82ccd1f45ee893d587e7a6f69/Mathlib/Data/Setoid/Partition.lean#L215-L215
def IsPartition {n : ℕ} (split : Split n) := ∅ ∉ split ∧ ∀ (f : Fin n), ∃! (cell : split), f ∈ (cell : Cell n)

theorem nonempty_of_mem_partition
    {n : ℕ}
    {split : Split n}
    (split_isPartition : split.IsPartition)
    {cell : Cell n}
    (cell_mem_split : cell ∈ split)
  : cell.Nonempty := by
    obtain ⟨empty_not_mem_split⟩ := split_isPartition
    apply Decidable.byContradiction
    intro cell_eq_empty
    simp at cell_eq_empty
    rw [cell_eq_empty] at cell_mem_split
    contradiction

end Split
