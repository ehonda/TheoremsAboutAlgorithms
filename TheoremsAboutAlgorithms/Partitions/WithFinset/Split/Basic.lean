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

def restrictCellCastPred {n : ℕ} (split : Split (n + 1)) (h : CastPredPrecondition split) (cell : split) : Cell n
  := cell.restrict (· ∈ split) Cell.castPred (h cell cell.property)

theorem restrictCellCastPred_injective {n : ℕ} (split : Split (n + 1)) (h : CastPredPrecondition split)
  : Function.Injective (restrictCellCastPred split h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictCellCastPred] at castPred_x_eq_castPred_y
    apply Subtype.eq
    -- TODO: Find out why this works with `exact`. The theorem states `x.castPred _ = y.castPred _ ↔ x = y`, but we
    --       don't have the left side here, just the restricted version:
    --          `Subtype.restrict (fun x ↦ x ∈ split) Cell.castPred' x _ = Subtype.restrict (fun x ↦ x ∈ split) Cell.castPred' y _`
    exact Cell.castPred_inj.mp castPred_x_eq_castPred_y

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
