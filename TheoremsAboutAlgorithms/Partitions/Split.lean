import Mathlib.Data.Setoid.Partition
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Cell

namespace Split

def cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Cell.cast h '' split

theorem cast_empty_not_mem_iff {n m : ℕ} (h : n = m) (split : Split n)
  : ∅ ∉ split.cast h ↔ ∅ ∉ split := by
    constructor <;> intro _ _ <;> simp [cast, Cell.cast] at * <;> contradiction

theorem cast_nonempty_iff {n m : ℕ} (h : n = m) (split : Split n)
  : (split.cast h).Nonempty ↔ split.Nonempty := by simp [cast]

def castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Cell.castSucc '' split

-- TODO: Fix naming elem -> mem
theorem castSucc_empty_elem_iff {n : ℕ} (split : Split n)
  : ∅ ∈ split.castSucc ↔ ∅ ∈ split := by simp [castSucc, Cell.castSucc]

def removeCell {n : ℕ} (split : Split n) (cell : Cell n) : Split n
  := split \ singleton cell

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := (split.removeCell targetCell).castSucc.insert targetCell.insertLast

theorem insertLastAt_castSucc_mem {n : ℕ} (split : Split n) (targetCell : Cell n)
  : targetCell.castSucc ∈ split.insertLastAt targetCell := by
    simp [insertLastAt, Cell.insertLast]
    sorry

theorem insertLastAt_Injective {n : ℕ} (split : Split n) : Function.Injective (split.insertLastAt) := by
  intro x y h
  --simp [insertLastAt] at h
  have := (Set.ext_iff (s := split.insertLastAt x) (t := split.insertLastAt y)).mp h x.castSucc
  --simp [insertLastAt] at *
  sorry

theorem insertLastAt_nonempty {n : ℕ} (split : Split n) (targetCell : Cell n)
  : (split.insertLastAt targetCell).Nonempty
    := Set.insert_nonempty _ _

-- TODO: Can we simplify this proof?
theorem insertLastAt_empty_not_mem_of_empty_not_mem
  {n : ℕ} (split : Split n) (targetCell : Cell n) (h : ∅ ∉ split) : ∅ ∉ split.insertLastAt targetCell := by
    simp [insertLastAt]
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
        have h_empty_mem_diff := (castSucc_empty_elem_iff (split \ {targetCell})).mp h_elem_removeCell
        contradiction

theorem insertLastAt_is_disjoint_insert {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Disjoint {targetCell.insertLast} (split.removeCell targetCell).castSucc := by
    apply disjoint_iff.mpr
    simp [removeCell, castSucc, Fin.castSucc]
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
def insertLast {n : ℕ} (split : Split n) : Set (Split (n + 1))
  := {split.insertLastAt cell | cell ∈ split.insert ∅}

theorem insertLast_nonempty_of_mem
  {n : ℕ}
  {split : Split n}
  {split' : Split (n + 1)}
  (h : split' ∈ insertLast split)
  : split'.Nonempty := by
    simp [insertLast] at h
    cases h with
      | intro cell h_cell =>
        rw [← h_cell.right]
        exact insertLastAt_nonempty _ _

def insertLast' {n : ℕ} (h : n > 0) (split : Split (n - 1)) : Set (Split n)
  := cast (Nat.sub_add_cancel h) '' split.insertLast

theorem insertLast'_nonempty_of_mem
  {n : ℕ}
  {h : n > 0}
  {split : Split (n - 1)}
  {split' : Split n}
  (h : split' ∈ insertLast' h split)
  : split'.Nonempty := by
    simp [insertLast'] at h
    cases h with
      | intro split'' h_split'' =>
        rw [← h_split''.right]
        have h_split''_nonempty : split''.Nonempty := insertLast_nonempty_of_mem h_split''.left
        simp [cast_nonempty_iff, h_split''_nonempty]

def IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

end Split
