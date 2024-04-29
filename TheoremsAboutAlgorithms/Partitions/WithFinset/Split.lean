import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Setoid.Partition
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

-- TODO: This is more general than last_not_mem_of_mem_removeCell_castSucc right? We don't need the other one
-- TODO: Rename, the naming seems of no? Should be last_not_mem_of_mem_castSucc?
theorem last_not_mem_of_mem_castSucc {n : ℕ} {split : Split n} {cell : Cell (n + 1)} (h : cell ∈ split.castSucc)
  : Fin.last n ∉ cell := by
    simp [castSucc, Cell.castSucc, Cell.castSuccEmbedding] at h
    cases h with
      | intro cell_pre h_cell_pre =>
        rw [← h_cell_pre.right]
        simp
        intro x _
        exact Fin.ne_of_lt (Fin.castSucc_lt_last x)

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := insert (targetCell.insertLast) (split.erase targetCell |> castSucc)

------------------------------------------------------------------------------------------------------------------------
--                          Bijections between split₀ and split.insertLastAt targetCell                               --
------------------------------------------------------------------------------------------------------------------------

-- WIP (I)

-- TODO: Injectivity of split.insertLastAt (as proved above) is not what we actually need in
--       `isPartition_of_mem_insertLast'_of_isPartition`. What we do need are functions f g such that
--
--          `f : split₀ → split.insertLastAt targetCell`
--          `g : split.insertLastAt targetCell → split₀`
--
--       and `f ∘ g = id` and `g ∘ f = id`. We want to define them as follows:
--
--          `f := if cell = targetCell then cell.insertLast else cell.castSucc`
--          `g := if cell = targetCell.insertLast then targetCell else cell.castPred`
--
--       To do that computably we need instances for `DecidableEq Cell`, which we will get by reimplementing `Cell` via
--       `Finset`. To see that what we plan to use them for [WIP (II)] works, we do it non-computably for now.

-- WIP (WithFinset.I)
--    * Find better names
--    * Prove that f and g are inverses
--    * Prove other useful stuff

def f'' {n : ℕ} (targetCell cell : Cell n) : Cell (n + 1)
  := if cell = targetCell then cell.insertLast else cell.castSucc

-- TODO: Remove the sorry (we probably need more assumpations?)
def g'' {n : ℕ} (targetCell : Cell n) (cell : Cell (n + 1)) : Cell n
  := if cell = targetCell.insertLast then targetCell else cell.castPred sorry

------------------------------------------------------------------------------------------------------------------------
--                                          insertLastAt, insertLast, ...                                             --
------------------------------------------------------------------------------------------------------------------------

theorem insertLastAt_nonempty {n : ℕ} (split : Split n) (targetCell : Cell n)
  : (split.insertLastAt targetCell).Nonempty
    := by simp [insertLastAt]

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
      · intro
        apply Set.disjoint_singleton_left.mp
        exact Cell.insertLast_is_disjoint_insert cell
    have := Set.ext_iff (s := cell.castSucc) (t := targetCell.insertLast)
    exact (not_congr this).mpr h_k

-- Helper prop
def InSplitInsertLastAtAndContainsLast {n : ℕ} (split : Split n) (targetCell : Cell n) (cell : Cell (n + 1)) : Prop
  := cell ∈ split.insertLastAt targetCell ∧ Fin.last n ∈ cell

theorem exists_contains_last {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∃ (cell : Cell (n + 1)), InSplitInsertLastAtAndContainsLast split targetCell cell := by
    simp [InSplitInsertLastAtAndContainsLast, insertLastAt, Set.insert, Cell.insertLast]

theorem unique_contains_last {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∀ (cell₁ cell₂ : Cell (n + 1)), InSplitInsertLastAtAndContainsLast split targetCell cell₁ → InSplitInsertLastAtAndContainsLast split targetCell cell₂ → cell₁ = cell₂ := by
    intros cell₁ cell₂ h₁ h₂
    simp [InSplitInsertLastAtAndContainsLast, insertLastAt, Set.insert] at *
    -- TODO: Factor out into lemma to not have to repeat this stuff
    have h_cell₁ : cell₁ = targetCell.insertLast := by
      have h_not_in_right : cell₁ ∉ (split.removeCell targetCell).castSucc := by
        -- TODO: Maybe we can do this without by_contra (since it isn't constructive is it?)
        by_contra h_in_right
        have h_last_not_mem := last_not_mem_of_mem_removeCell_castSucc split targetCell cell₁ h_in_right
        have h_last_mem := h₁.right
        contradiction
      apply (or_iff_left (a := cell₁ = targetCell.insertLast) (b := cell₁ ∈ (split.removeCell targetCell).castSucc) h_not_in_right).mp
      exact h₁.left
    have h_cell₂ : cell₂ = targetCell.insertLast := by
      have h_not_in_right : cell₂ ∉ (split.removeCell targetCell).castSucc := by
        by_contra h_in_right
        have h_last_not_mem := last_not_mem_of_mem_removeCell_castSucc split targetCell cell₂ h_in_right
        have h_last_mem := h₂.right
        contradiction
      apply (or_iff_left (a := cell₂ = targetCell.insertLast) (b := cell₂ ∈ (split.removeCell targetCell).castSucc) h_not_in_right).mp
      exact h₂.left
    rw [h_cell₁, h_cell₂]

-- NOTE: This can be used in insertLast'_produces_partitions
theorem insertLastAt_unique_cell_last_mem {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∃! (cell : Cell (n + 1)), InSplitInsertLastAtAndContainsLast split targetCell cell
    := exists_unique_of_exists_of_unique (exists_contains_last split targetCell) (unique_contains_last split targetCell)

theorem insertLastAt_castSucc_mem_of_mem_of_ne_targetCell
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : Cell n}
    (h_mem : cell ∈ split)
    (h_ne : cell ≠ targetCell)
  : cell.castSucc ∈ split.insertLastAt targetCell := by
    simp [insertLastAt, Set.insert, Split,castSucc]
    right
    exists cell

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- TODO: Do we even need this if we have the version below?
def insertLast {n : ℕ} (split : Split n) : Set (Split (n + 1))
  := {split.insertLastAt cell | cell ∈ split.insert ∅}

theorem insertLastAt_mapsTo {n : ℕ} (split : Split n)
  : Set.MapsTo split.insertLastAt (split.insert ∅) split.insertLast := by
    simp [Set.MapsTo, insertLast]
    intro cell cell_mem_split
    exists cell

-- TODO: Use insertLastAt_mapsTo here
theorem insertLastAt_surjOn {n : ℕ} (split : Split n)
  : Set.SurjOn split.insertLastAt (split.insert ∅) split.insertLast := by
    simp [Set.SurjOn, insertLast, Set.image]
    intro cell cell_mem_split'
    exists cell

theorem insertLastAt_bijOn {n : ℕ} (split : Split n)
  : Set.BijOn split.insertLastAt (split.insert ∅) split.insertLast := by
    split_ands
    · exact insertLastAt_mapsTo split
    · exact insertLastAt_injOn split
    · exact insertLastAt_surjOn split

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

-- TODO: Probably fix this by mapping Finset.toSet
def IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

end Split
