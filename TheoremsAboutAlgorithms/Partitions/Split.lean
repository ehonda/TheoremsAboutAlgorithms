import Mathlib.Data.Setoid.Partition
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Cell

namespace Split

def cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Cell.cast h '' split

theorem cast_empty_not_mem_iff {n m : ℕ} (h : n = m) (split : Split n)
  : ∅ ∉ split.cast h ↔ ∅ ∉ split := by
    constructor <;> intro _ _ <;> simp [cast, Cell.cast] at * <;> contradiction

theorem cast_mem_iff {n : ℕ} (split : Split n) (cell : Cell n)
  : cell ∈ split.cast rfl ↔ cell ∈ split := by simp [cast, Cell.cast]

theorem cast_nonempty_iff {n m : ℕ} (h : n = m) (split : Split n)
  : (split.cast h).Nonempty ↔ split.Nonempty := by simp [cast]

def castSucc {n : ℕ} (split : Split n) : Split (n + 1)
  := Cell.castSucc '' split

theorem castSucc_injective {n : ℕ} : Function.Injective (castSucc (n := n)) := by
  intro x y h
  simp [castSucc] at h
  have Cell.castSucc_injective_on_split := Function.Injective.image_injective (Cell.castSucc_injective (n := n))
  exact Cell.castSucc_injective_on_split h

-- TODO: Fix naming elem -> mem
theorem castSucc_empty_elem_iff {n : ℕ} (split : Split n)
  : ∅ ∈ split.castSucc ↔ ∅ ∈ split := by simp [castSucc, Cell.castSucc]

-- TODO: This is more general than last_not_mem_of_mem_removeCell_castSucc right? We don't need the other one
-- TODO: Rename, the naming seems of no? Should be last_not_mem_of_mem_castSucc?
theorem castSucc_last_not_mem_of_mem {n : ℕ} {split : Split n} {cell : Cell (n + 1)} (h : cell ∈ split.castSucc)
  : Fin.last n ∉ cell := by
    simp [castSucc, Cell.castSucc] at h
    cases h with
      | intro cell_pre h_cell_pre =>
        rw [← h_cell_pre.right]
        simp
        intro x _
        exact Fin.ne_of_lt (Fin.castSucc_lt_last x)

def removeCell {n : ℕ} (split : Split n) (cell : Cell n) : Split n
  := split \ singleton cell

-- TODO: Maybe we can find a better name yet (it's alright, but not totally satisfactory).
-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {targetCell.transform} ∪ (split \ {targetCell})
def insertLastAt {n : ℕ} (split : Split n) (targetCell : Cell n) : Split (n + 1)
  := insert (targetCell.insertLast) (split.removeCell targetCell).castSucc

------------------------------------------------------------------------------------------------------------------------
--                                          Injectivity of insertLastAt                                               --
------------------------------------------------------------------------------------------------------------------------

theorem insertLastAt_injOn_helper_generalized_subset_helper
    {n : ℕ}
    {cell otherCell : Cell n}
    {split otherSplit : Split (n + 1)}
    (split'_eq_otherSplit' : insert cell.insertLast split = insert otherCell.insertLast otherSplit)
    (last_not_mem_of_mem_split : ∀ cell, cell ∈ split → Fin.last n ∉ cell)
  : split ⊆ otherSplit := by
    intro x x_mem_split
    have x_mem_insert_insertLast_otherCell_otherSplit : x ∈ insert otherCell.insertLast otherSplit := by
      rw [← split'_eq_otherSplit']; simp; right; exact x_mem_split
    cases x_mem_insert_insertLast_otherCell_otherSplit with
      | inl x_eq_insertLast_otherCell =>
        have last_mem_x := Cell.last_mem_insertLast otherCell
        rw [← x_eq_insertLast_otherCell] at last_mem_x
        have last_not_mem_x := last_not_mem_of_mem_split x x_mem_split
        contradiction
      | inr x_mem_otherSplit => exact x_mem_otherSplit

-- TODO: NAMING!
theorem insertLastAt_injOn_helper_generalized
    {n : ℕ}
    {cell otherCell : Cell n}
    {split otherSplit : Split (n + 1)}
    (split'_eq_otherSplit' : insert cell.insertLast split = insert otherCell.insertLast otherSplit)
    (last_not_mem_of_mem_split : ∀ cell, cell ∈ split → Fin.last n ∉ cell)
    (last_not_mem_of_mem_otherSplit : ∀ cell, cell ∈ otherSplit → Fin.last n ∉ cell)
  : split = otherSplit := by
    -- TODO: We know that insertLast is injective, use it here!
    -- TODO: Totally symmetric, can we wlog it?
    apply Set.eq_of_subset_of_subset
    · exact insertLastAt_injOn_helper_generalized_subset_helper split'_eq_otherSplit' last_not_mem_of_mem_split
    · exact insertLastAt_injOn_helper_generalized_subset_helper
        split'_eq_otherSplit'.symm last_not_mem_of_mem_otherSplit

theorem insertLastAt_injOn_helper
    {n : ℕ}
    {cell otherCell : Cell n}
    {split : Split n}
    (h : insert cell.insertLast (split.removeCell cell).castSucc
          = insert otherCell.insertLast (split.removeCell otherCell).castSucc)
  : (split.removeCell cell).castSucc = (split.removeCell otherCell).castSucc := by
    have last_not_mem_of_mem_split' : ∀ x, x ∈ (split.removeCell cell).castSucc → Fin.last n ∉ x
      := by intro _ x_mem_split'; exact castSucc_last_not_mem_of_mem x_mem_split'
    have last_not_mem_of_mem_otherSplit' : ∀ x, x ∈ (split.removeCell otherCell).castSucc → Fin.last n ∉ x
      := by intro _ x_mem_split'; exact castSucc_last_not_mem_of_mem x_mem_split'
    exact insertLastAt_injOn_helper_generalized h last_not_mem_of_mem_split' last_not_mem_of_mem_otherSplit'

-- TODO: Proof it
theorem insertLastAt_injOn_disjoint_helper
    {n : ℕ}
    (x y : Cell n)
    (split : Split n)
  : Disjoint {x.insertLast} (split.removeCell y).castSucc := by
    simp
    have last_mem_insertLast_x := Cell.last_mem_insertLast x
    have last_not_mem_of_mem_split' : ∀ cell, cell ∈ (split.removeCell y).castSucc → (Fin.last _) ∉ cell
      := by intro cell cell_mem_split'; exact castSucc_last_not_mem_of_mem cell_mem_split'
    intro insertLast_x_mem_split'
    have last_not_mem_insertLast_x := last_not_mem_of_mem_split' x.insertLast insertLast_x_mem_split'
    contradiction

theorem insertLastAt_injOn_symmetric_case_helper
    {n : ℕ}
    {split : Split n}
    {x y : Cell n}
    (insertLastAt_x_eq_insertLastAt_y : split.insertLastAt x = split.insertLastAt y)
    (x_eq_empty : x = ∅)
  : x = y := by
    -- TODO: Do we need all these have's? We can probably get rid of some of them
    have singleton_last_mem_split'_x : {Fin.last _} ∈ split.insertLastAt x := by
      simp [x_eq_empty, insertLastAt, Set.insert, Cell.insertLast, Cell.castSucc]
        at insertLastAt_x_eq_insertLastAt_y ⊢
    have singleton_last_mem_split'_y : {Fin.last _} ∈ split.insertLastAt y := by
      rw [← insertLastAt_x_eq_insertLastAt_y]
      exact singleton_last_mem_split'_x
    have singleton_last_eq_y_insertLast : {Fin.last _} = y.insertLast := by
      simp [insertLastAt, Cell.insertLast] at singleton_last_mem_split'_y
      cases singleton_last_mem_split'_y with
        | inl singleton_last_mem_set_insert =>
          simp [Cell.insertLast]
          exact singleton_last_mem_set_insert
        | inr singleton_last_mem_removeCell =>
          have := castSucc_last_not_mem_of_mem singleton_last_mem_removeCell
          contradiction
    have y_eq_empty : y = ∅ := by
      simp [Cell.insertLast] at singleton_last_eq_y_insertLast
      -- For some reason simp times out if we use it there
      rw [Set.insert_eq (Fin.last n) (Cell.castSucc y)] at singleton_last_eq_y_insertLast
      have castSucc_y_subset_singleton_last : Cell.castSucc y ⊆ {Fin.last _} := by
        rw [singleton_last_eq_y_insertLast]
        exact Set.subset_union_right _ _
      have castSucc_y_Subsingleton : Set.Subsingleton (Cell.castSucc y)
        := Set.subsingleton_of_subset_singleton castSucc_y_subset_singleton_last
      have := Set.Subsingleton.eq_empty_or_singleton castSucc_y_Subsingleton
      cases this with
        | inl y_eq_empty => exact (Cell.castSucc_empty_iff y).mp y_eq_empty
        | inr y_eq_singleton =>
          -- TODO: Naming
          obtain ⟨y_mem, y_mem_def⟩ := y_eq_singleton
          have y_mem_eq_last : y_mem = Fin.last _ := by
            rw [y_mem_def] at castSucc_y_subset_singleton_last
            simp at castSucc_y_subset_singleton_last
            exact castSucc_y_subset_singleton_last
          have y_mem_ne_last : y_mem ≠ Fin.last _ := by
            have exists_castSucc_eq_y_mem : ∃ (y' : Fin n), y'.castSucc = y_mem := by
              rw [y_mem_eq_last]
              simp [Cell.castSucc, Set.image] at y_mem_def
              have : ∃ a ∈ y, Fin.castSucc a = y_mem := by
                have : y_mem ∈ {x | ∃ a ∈ y, Fin.castSucc a = x} := by
                  have := Set.mem_singleton y_mem
                  rw [← y_mem_def] at this
                  exact this
                exact Set.mem_setOf.mp this
              rw [y_mem_eq_last] at this
              obtain ⟨y', _, y'_eq_y_mem⟩ := this
              exists y'
            exact Fin.exists_castSucc_eq.mp exists_castSucc_eq_y_mem
          contradiction
    rw [x_eq_empty, y_eq_empty]

theorem insertLastAt_injOn {n : ℕ} (split : Split n)
  : Set.InjOn (split.insertLastAt) (split.insert ∅) := by
    intros x x_mem_split' y y_mem_split' insertLastAt_x_eq_insertLastAt_y
    cases x_mem_split' with
      | inl x_eq_empty =>
        cases y_mem_split' with
          | inl y_eq_empty => rw [x_eq_empty, y_eq_empty]
          | inr y_mem_split =>
            exact insertLastAt_injOn_symmetric_case_helper insertLastAt_x_eq_insertLastAt_y x_eq_empty
      | inr x_mem_split =>
        cases y_mem_split' with
          | inl y_eq_empty =>
            exact (insertLastAt_injOn_symmetric_case_helper insertLastAt_x_eq_insertLastAt_y.symm y_eq_empty).symm
          | inr y_mem_split =>
            simp [insertLastAt] at insertLastAt_x_eq_insertLastAt_y
            have castSucc_eq : (split.removeCell x).castSucc = (split.removeCell y).castSucc
              := insertLastAt_injOn_helper insertLastAt_x_eq_insertLastAt_y
            rw [castSucc_eq] at insertLastAt_x_eq_insertLastAt_y
            repeat rw [Set.insert_eq] at insertLastAt_x_eq_insertLastAt_y
            -- TODO: There's probably a more straightforward way to do this
            have singleton_insertLast_x_subset_y_union : {Cell.insertLast x} ⊆ {Cell.insertLast y} ∪ castSucc (removeCell split y) := by
              have := Set.subset_union_left {Cell.insertLast x} (castSucc (split.removeCell y))
              rw [insertLastAt_x_eq_insertLastAt_y] at this
              exact this
            have singleton_insertLast_x_subsetsingleton_insertLast_y : {Cell.insertLast x} ⊆ ({Cell.insertLast y} : (Split (n + 1))) := by
              have singleton_insertLast_x_disjoint_castSucc := insertLastAt_injOn_disjoint_helper x y split
              exact Disjoint.subset_left_of_subset_union singleton_insertLast_x_subset_y_union singleton_insertLast_x_disjoint_castSucc
            have : Cell.insertLast x = Cell.insertLast y := by
              apply Set.singleton_subset_singleton.mp
              exact singleton_insertLast_x_subsetsingleton_insertLast_y
            exact Cell.insertLast_injective this

------------------------------------------------------------------------------------------------------------------------
--                                          End Injectivity of insertLastAt                                           --
------------------------------------------------------------------------------------------------------------------------

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

theorem last_not_mem_of_mem_removeCell_castSucc {n : ℕ} (split : Split n) (targetCell : Cell n) (cell : Cell (n + 1)) (h : cell ∈ (split.removeCell targetCell).castSucc)
  : Fin.last n ∉ cell := by
    simp [removeCell, castSucc, Fin.castSucc] at h
    cases h with
      | intro cell_pre h_cell_pre =>
        rw [← h_cell_pre.right]
        simp [Cell.castSucc]
        intro x _
        exact Fin.ne_of_lt (Fin.castSucc_lt_last x)

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

def IsPartition {n : ℕ} (split : Split n) : Prop
  := Setoid.IsPartition split

end Split
