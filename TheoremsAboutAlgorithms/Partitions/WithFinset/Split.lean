import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Setoid.Partition
import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs
import TheoremsAboutAlgorithms.Partitions.WithFinset.Cell

namespace Split

def cast {n m : ℕ} (h : n = m) (split : Split n) : Split m
  := Finset.map (Cell.castEmbedding h) split

theorem empty_not_mem_cast_iff_empty_not_mem {n m : ℕ} (h : n = m) (split : Split n)
  : ∅ ∉ split.cast h ↔ ∅ ∉ split := by
    constructor <;> intro _ _ <;> simp [cast, Cell.castEmbedding, Cell.cast] at * <;> contradiction

theorem mem_cast_iff_mem {n : ℕ} (split : Split n) (cell : Cell n)
  : cell ∈ split.cast rfl ↔ cell ∈ split := by
    constructor
    <;> intro
    <;> simp [cast, Cell.castEmbedding, Cell.cast, Fin.castEmbedding, Finset.map] at *
    <;> assumption

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

-- Alternative definitions 2

-- WIP (I.III)
--    * Here we move the restrictions on the source and target domain of f and g from the types into the propositions,
--      because right now it's kind of hard to get the types right (and this is intended to be a mere POC anyway)
--    * Otherwise, we do the same as in WIP (I.II)

theorem exists_f' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∃ (f : Cell n → Cell (n + 1)),
    ∀ (cell : Cell n), cell ∈ split.insert ∅ →
      (cell = targetCell → f cell ∈ split.insertLastAt targetCell ∧ f cell = targetCell.insertLast)
      ∧ (cell ≠ targetCell → f cell ∈ split.insertLastAt targetCell ∧ f cell = cell.castSucc) := by
        sorry

noncomputable def f' {n : ℕ} (split : Split n) (targetCell : Cell n) : Cell n → Cell (n + 1)
  := (exists_f' split targetCell).choose

theorem exists_g' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∃ (g : Cell (n + 1) → Cell n),
    ∀ (cell : Cell (n + 1)), cell ∈ split.insertLastAt targetCell →
      (cell = targetCell.insertLast → g cell ∈ split.insert ∅ ∧ g cell = targetCell)
      ∧ (cell ≠ targetCell.insertLast → g cell ∈ split.insert ∅ ∧ g cell = cell.castPred sorry) := by
        sorry

noncomputable def g' {n : ℕ} (split : Split n) (targetCell : Cell n) : Cell (n + 1) → Cell n
  := (exists_g' split targetCell).choose

theorem leftInverse_f'_g' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Function.LeftInverse (f' split targetCell) (g' split targetCell) := by
    sorry

theorem rightInverse_f'_g' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Function.RightInverse (f' split targetCell) (g' split targetCell) := by
    sorry

-- TODO: Use Function.bijective_iff_has_inverse for these
theorem bijective_f' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Function.Bijective (f' split targetCell) := by
    sorry

theorem bijective_g' {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Function.Bijective (g' split targetCell) := by
    sorry

-- Alternative definitions

-- WIP (I.II)
--    * This should be the better approach, defining directly what f and g look like at the different value pattern.
--    * We should then (non-constructively) be able to proof left- / right-inverse by using `eq_or_ne` and accessing the
--      definition of the values of f and g at the different value patterns.
--    * Can we use `CoeDep` [0] to show that `Cell.castSucc cell : ↑(split.insertLastAt targetCell)`?. The instance
--      below looks like it should help but it doesn't. The problem probably is that we use it in a type and so we need
--      `CoeSort`?
--    * Maybe there's something wrong with our `CoeDep`, `test2` should work (we coerce a value right?), but it doesn't
--
--    [0] https://lean-lang.org/functional_programming_in_lean/type-classes/coercion.html#non-empty-lists-and-dependent-coercions

def nonTarget {n : ℕ} (split : Split n) (targetCell : Cell n) : Split n
  := removeCell (split.insert ∅) targetCell

theorem coe_castSucc_cell
    {n : ℕ}
    (split : Split n)
    (targetCell : Cell n)
    (cell : ↑(split.nonTarget targetCell))
  : Cell.castSucc cell ∈ split.insertLastAt targetCell := by
    simp [insertLastAt, Set.insert, Cell.castSucc]
    right
    exists cell
    sorry

-- We would rather have `cell_ne_targetCell : ↑cell ≠ targetCell` here but we don't know how to make it so that the
-- coercion can then be found below, so we directly put it into the cell's type.
instance
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : ↑(split.nonTarget targetCell)}
  : CoeDep (Cell (n + 1)) (Cell.castSucc cell) ↑(split.insertLastAt targetCell) where
    coe := by
      use Cell.castSucc cell
      exact coe_castSucc_cell split targetCell cell

-- Here we state the definition of f via propostions, because for a direct definition we need decidable equality on
-- Cell. We can then noncomputably choose a function that satisfies the propositions.
-- theorem exists_f {n : ℕ} (split : Split n) (targetCell : Cell n)
--   : ∃ (f : ↑(split.insert ∅) → ↑(split.insertLastAt targetCell)),
--     ∀ (cell : ↑(split.insert ∅)), (cell = targetCell → f cell = targetCell.insertLast)
--       -- We have to explicitly specify `Cell (n + 1)` here such that the dependent coercion specified above can be found
--       ∧ (↑cell ∈ split.nonTarget targetCell → f cell = ↑(Cell.castSucc (↑cell : ↑(split.nonTarget targetCell)) : Cell (n + 1))) := by
--       sorry

theorem exists_f_g {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ∃ (f : ↑(split.insert ∅) → ↑(split.insertLastAt targetCell)),
    ∃ (g : ↑(split.insertLastAt targetCell) → ↑(split.insert ∅)),
    Function.LeftInverse f g ∧ Function.RightInverse f g := by
      sorry

noncomputable def f {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ↑(split.insert ∅) → ↑(split.insertLastAt targetCell) :=
    (exists_f_g split targetCell).choose

-- TODO: Fix, how do we get to choose on the second exists?
noncomputable def g {n : ℕ} (split : Split n) (targetCell : Cell n)
  : ↑(split.insertLastAt targetCell) → ↑(split.insert ∅) :=
    (exists_f_g split targetCell).choose_spec.choose

-- TODO: Show this (as an exercise)
example {n : ℕ} (split : Split n) (targetCell : Cell n)
  : Function.LeftInverse (f split targetCell) (g split targetCell)
    := (exists_f_g split targetCell).choose_spec.choose_spec.left

-- We don't need this. We can use it for `(tcast split ▸ targetCell)` if `targetCell : ↑(split.insert ∅)`, but we don't
-- have to actually do this since there is `Set.instCoeSortSetType  {α : Type u} : CoeSort (Set α) (Type u)` which
-- is the "Coercion from a set to the corresponding subtype." so we can just use `targetCell : split.insert ∅` in places
-- where we `targetCell : Cell n` is expected.
theorem tcast
    {n : ℕ}
    (split : Split n)
  : ↑(Set.insert ∅ split) = Cell n := by
    sorry

-- This is just `Set.instCoSortSetType`, we don't need it.
--instance {n : ℕ} {split : Split n} : CoeSort ↑(Set.insert ∅ split) (Cell n) where
--  coe cell := cell

-- TODO: Fix, this is wrong!
theorem icast
    {n : ℕ}
    (split : Split n)
    (targetCell : ↑(split.insert ∅))
  : Cell (n + 1) = ↑(split.insertLastAt targetCell) := by
  --: ↑(Cell.insertLast targetCell) = ↑(split.insertLastAt targetCell) := by
    sorry

--instance {n : ℕ} {split : Split n} {targetCell : ↑(split.insert ∅)} : CoeSort (Cell (n + 1)) ↑(split.insertLastAt targetCell) where
--  coe cell := sorry

-- WIP (I.I)
--    * Can we get rid of icast? Do we need an instance for that?
--      * What does this error mean if we uncomment the second instance:
--        ```
--        instance does not provide concrete values for (semi-)out-params
--          CoeSort (Cell (n + 1)) ↑(insertLastAt ?split ↑?targetCell)
--        ```
--    * `icast` looks questionable, we cast a Cell to "the type of elements of a split", which we can't do in general,
--      because the cell need not be in the split. We probably need something along those lines (or the reverse?):
--      ```
--      ↑(Cell.insertLast targetCell) = ↑(split.insertLastAt targetCell)
--      ```

theorem f_targetCell_eq_targetCell_insertLast_with_instances
    {n : ℕ}
    (split : Split n)
    (targetCell : ↑(split.insert ∅))
    : f split targetCell targetCell
        = ((icast split targetCell ▸ Cell.insertLast targetCell)
            : ↑(insertLastAt split targetCell))
      := by sorry

--theorem f_targetCell_eq_targetCell_insertLast
--    {n : ℕ}
--    (split : Split n)
--    (targetCell : ↑(split.insert ∅))
--    : f split (tcast split ▸ targetCell) targetCell
--        = ((icast split targetCell ▸ Cell.insertLast (tcast split ▸ targetCell))
--            : ↑(insertLastAt split (tcast split ▸ targetCell)))
--      := by sorry

------------------------------------------------------------------------------------------------------------------------
--                                          insertLastAt, insertLast, ...                                             --
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
