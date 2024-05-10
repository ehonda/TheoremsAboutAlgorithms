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
--                          Bijections between split₀ and split.insertLastAt targetCell                               --
------------------------------------------------------------------------------------------------------------------------

-- WIP (I)

-- What we want and define here are functions `f` and `g` (which will have more descriptive names below) such that
--
--    `f : split → split.insertLastAt targetCell`
--    `g : split.insertLastAt targetCell → split`
--
-- and `f ∘ g = id` and `g ∘ f = id`. We want to define them as follows:
--
--    `f := if cell = targetCell then cell.insertLast else cell.castSucc`
--    `g := if cell = targetCell.insertLast then targetCell else cell.castPred`
--
-- To do that we need an assumption `{Fin.last _} ∉ split.insertLastAt targetCell` to be able to define `g` as above,
-- because that has the preimage `∅` which we can't include in the domain of `f` (and therefore also not in the codomain
-- of `g`).
--
-- TODO: See in the usage later if that is what we actually need. Maybe we can `split.insertEmpty` work as domain of `f`
--       as codomain of `g` as well.

-- TODO:
--    * Prove that f and g are inverses
--    * Prove other useful stuff
--    * Theorem names and naming in general in this section are lacking, improve them!

-- TODO: Make this a section and define all the common implicit arguments (`n, split, targetCell`) at the top
theorem insertLast_mem_insertLastAt_of_eq
    {n : ℕ}
    {split : Split n}
    {targetCell cell : Cell n}
    (cell_eq_targetCell : cell = targetCell)
  : cell.insertLast ∈ split.insertLastAt targetCell := by
    simp [insertLastAt]
    left
    rw [cell_eq_targetCell]

-- TODO: How can we make this anonymous so it can be found implicitly if we have the equality hypothesis?
--       Maybe this resource can help find the answer:
--        https://leanprover-community.github.io/mathlib4_docs/Init/Coe.html
--
--      Maybe `#print toInsertLastAt` can help us find the answer.
instance CoeDepInsertLastInsertLastAtOfEq
    {n : ℕ}
    {split : Split n}
    {targetCell cell : Cell n}
    (cell_eq_targetCell : cell = targetCell)
  : CoeDep (Cell (n + 1)) (cell.insertLast) (split.insertLastAt targetCell) where
    coe := by
      use cell.insertLast
      exact insertLast_mem_insertLastAt_of_eq cell_eq_targetCell

-- We can't have `cell : split.insertEmpty`, because `Cell.castSucc ∅` is not in fact in `split.insertLastAt`. We do
-- however want to use this in the situation where `split` is a partition meaning that `∅ ∉ split`. We only use
-- `partitions.insertEmpty` there the have a target for the to create `{Fin.last _}`. We probably do not need to have
-- `insertEmptyToInsertLastAt` to go from `partition.insertEmpty` but can use just `partition` as the domain. We handle
-- the case where `cell = ∅` separately.
theorem castSucc_mem_insertLastAt_of_ne
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split}
    (cell_ne_targetCell : ↑cell ≠ targetCell)
  : Cell.castSucc cell ∈ split.insertLastAt targetCell := by
    simp [insertLastAt, castSucc, Cell.castSuccEmbedding, Cell.castSucc]
    right
    assumption

-- TODO: How can we make this anonymous (like above)?
instance CoeDepCastSuccInsertLastAtOfNe
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split}
    (cell_ne_targetCell : ↑cell ≠ targetCell)
  : CoeDep (Cell (n + 1)) (Cell.castSucc cell) (split.insertLastAt targetCell) where
    coe := by
      use Cell.castSucc cell
      exact castSucc_mem_insertLastAt_of_ne cell_ne_targetCell

def upward
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    (cell : split)
  : split.insertLastAt targetCell :=
    if h : cell = targetCell
    -- CoeDep.coe.{u, v} {α : Sort u} (x✝ : α) {β : Sort v} [self : CoeDep α x✝ β] : β
    -- then CoeDep.coe _ (Cell.castSucc cell) _ (CoeDepInsertLastInsertLastAtOfEq h)
    then (CoeDepInsertLastInsertLastAtOfEq h).coe
    else (CoeDepCastSuccInsertLastAtOfNe h).coe

-- TODO: Naming feels pretty imprecise here
theorem ne_last_of_ne_insertLast_of_mem
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_targetCell_insertLast : ↑cell ≠ targetCell.insertLast)
    (x : ↑cell)
  : ↑x ≠ Fin.last n := by
    have cell_mem_insertLastAt := cell.property
    simp [insertLastAt] at cell_mem_insertLastAt
    cases cell_mem_insertLastAt with
      | inl _ => contradiction
      | inr cell_mem_castSucc =>
        apply Decidable.byContradiction
        intro x_eq_last
        simp at x_eq_last
        have last_mem_cell : Fin.last n ∈ (cell : Cell (n + 1)) := by
          have := x.property;
          rw [x_eq_last] at this;
          exact this
        have last_not_mem_cell := last_not_mem_of_mem_castSucc cell_mem_castSucc
        contradiction

-- TODO: Naming feels pretty imprecise here
theorem ne_last_of_ne_insertLast
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_targetCell_insertLast : ↑cell ≠ targetCell.insertLast)
  : ∀ x ∈ (cell : Cell (n + 1)), ↑x ≠ Fin.last n := by
    intro x x_mem_cell
    exact ne_last_of_ne_insertLast_of_mem cell_ne_targetCell_insertLast ⟨x, x_mem_cell⟩

theorem mem_castSucc_of_ne_targetCell_of_mem_castSucc_erase_targetCell
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : Cell (n + 1)}
    (cell_mem_castSucc_erase_targetCell : cell ∈ (split.erase targetCell |> castSucc))
  : cell ∈ split.castSucc := by
      simp [castSucc, Cell.castSuccEmbedding] at *
      obtain ⟨_, cell', _, _⟩ := cell_mem_castSucc_erase_targetCell
      use cell'

-- cell'_mem_split : cell' ∈ split
-- castSucc_cell'_eq_cell : Cell.castSucc cell' = ↑cell
-- ⊢ Cell.castPred ↑cell _ ∈ split
theorem castPred_mem_split_of_mem_split_of_castSucc_eq_of_last_not_mem
    {n : ℕ}
    {split : Split n}
    {x : Cell n}
    {y : Cell (n + 1)}
    (x_mem_split : x ∈ split)
    (castSucc_x_eq_y : Cell.castSucc x = y)
    (last_not_mem_y : ∀ f ∈ y, f ≠ Fin.last _)
  : Cell.castPred y last_not_mem_y ∈ split := by
    -- See https://proofassistants.stackexchange.com/a/1063 for why we use `subst` here
    rw [Cell.castPred_y_eq_x_of_castSucc_x_eq_y_of_forall_mem_y_ne_last castSucc_x_eq_y last_not_mem_y]
    exact x_mem_split

theorem castPred_mem_of_ne_insertLast_of_mem_castSucc
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_insertLast_targetCell : ↑cell ≠ targetCell.insertLast)
    (cell_mem_castSucc : ↑cell ∈ split.castSucc)
  : (Cell.castPred cell) (ne_last_of_ne_insertLast cell_ne_insertLast_targetCell) ∈ split := by
    simp [castSucc, Cell.castSuccEmbedding] at cell_mem_castSucc
    obtain ⟨cell', cell'_mem_split, castSucc_cell'_eq_cell⟩ := cell_mem_castSucc
    -- We use the helper because `rw` and `subst` do not work here (probably because we're coercing `cell` via `↑cell`)
    apply castPred_mem_split_of_mem_split_of_castSucc_eq_of_last_not_mem cell'_mem_split castSucc_cell'_eq_cell

theorem castPred_mem_of_mem_insertLastAt_of_ne_targetCell
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_insertLast_targetCell : ↑cell ≠ targetCell.insertLast)
  : (Cell.castPred cell) (ne_last_of_ne_insertLast cell_ne_insertLast_targetCell) ∈ split := by
    have cell_mem_insertLastAt := cell.property
    simp [insertLastAt] at cell_mem_insertLastAt
    cases cell_mem_insertLastAt with
      | inl cell_eq_targetCell_insertLast => contradiction
      | inr cell_mem_castSucc =>
        apply castPred_mem_of_ne_insertLast_of_mem_castSucc cell_ne_insertLast_targetCell
        exact mem_castSucc_of_ne_targetCell_of_mem_castSucc_erase_targetCell cell_mem_castSucc

instance CoeDepCastPredOfNeInsertLast
    {n : ℕ}
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_insertLast_targetCell : ↑cell ≠ targetCell.insertLast)
  : CoeDep (Cell n) ((Cell.castPred cell) (ne_last_of_ne_insertLast cell_ne_insertLast_targetCell)) split where
    coe := by
      use (Cell.castPred cell) (ne_last_of_ne_insertLast cell_ne_insertLast_targetCell)
      exact castPred_mem_of_mem_insertLastAt_of_ne_targetCell cell_ne_insertLast_targetCell

-- TODO: This should probably be defined for `cell ≠ {Fin.last _}`, we just handle that case differently, so we have the
--       codomain equal to `toInsertLastAt`'s domain
def downward
    {n : ℕ}
    (split : Split n)
    (targetCell : split)
    (cell : split.insertLastAt targetCell)
  : split :=
    if h : cell = Cell.insertLast (targetCell : Cell n)
    then targetCell
    else (CoeDepCastPredOfNeInsertLast h).coe

-- ∃ (h : Cell.castPred ↑x _ ∈ split),

-- Surjectivity
-- TODO: Finish this proof
theorem upward_surjective
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Surjective (@upward _ split targetCell) := by
    intro x
    simp [upward]
    -- TODO: Make this work
    -- TODO: Find a way we can use better notation than the explicit long instance name
    -- let y := (@CoeDepInsertLastInsertLastAtOfEq n _ _ ).coe
    cases Decidable.eq_or_ne x (CoeDepInsertLastInsertLastAtOfEq rfl).coe with
      | inl x_eq_coe_insertLast_targetCell =>
        exists targetCell
        exists targetCell.property
        split
        · exact x_eq_coe_insertLast_targetCell.symm
        · contradiction
      | inr x_ne_coe_insertLast_targetCell =>
        have x_val_ne_insertLast_targetCell : (x : Cell (n + 1)) ≠ Cell.insertLast ↑targetCell := by
          simp [CoeDep.coe] at *
          intro x_val_eq_insertLast_targetCell
          have : x = (CoeDepInsertLastInsertLastAtOfEq rfl).coe := by
            apply @Subtype.eq _ _ x _
            exact x_val_eq_insertLast_targetCell
          contradiction
        -- If we use this (instead of writing out the verbose expression), this makes `castPred_h_x` appear everywhere
        -- we would otherwise have `_` in the proof state which is ugly
        -- let castPred_h_x := (ne_last_of_ne_insertLast x_val_ne_insertLast_targetCell)
        -- TODO: How can we make it that we put this into the context and it is found implicitly?
        exists Cell.castPred x (ne_last_of_ne_insertLast x_val_ne_insertLast_targetCell)
        have castPred_x_val_mem_split : Cell.castPred x (ne_last_of_ne_insertLast x_val_ne_insertLast_targetCell) ∈ split := by
          sorry
        exists castPred_x_val_mem_split
        split
        · case _ castPred_x_val_eq_targetCell_val =>
          have : (x : Cell (n + 1)) = Cell.insertLast ↑targetCell := by
            sorry
          contradiction
        · case _ castPred_x_val_ne_insertLast_targetCell =>
          simp [CoeDep.coe]
          apply Subtype.eq
          simp [Cell.castSucc_castPred_eq]

-- Inverses

theorem left_inverse_downward_upward
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.LeftInverse (@downward _ split targetCell) (@upward _ split targetCell) := by
    intro x
    simp [upward, downward]
    split
    · case _ x_eq_targetCell =>
      split
      · apply Subtype.eq
        exact x_eq_targetCell.symm
      · case _ insertLast_x_ne_insertLast_targetCell =>
        simp [CoeDep.coe] at insertLast_x_ne_insertLast_targetCell
        -- TODO: There has to be a better way to get f x = f y from x = y
        have : Cell.insertLast ↑x = Cell.insertLast (targetCell : Cell n) := by
          have : Cell.insertLast ↑x = Cell.insertLast (x : Cell n) := by rfl
          rw (config := {occs := .pos [2]}) [x_eq_targetCell] at this
          exact this
        contradiction
    · case _ x_ne_targetCell_insertLast =>
      split
      · case _ castSucc_x_eq_insertLast_targetCell =>
        simp [CoeDep.coe] at castSucc_x_eq_insertLast_targetCell
        have := Cell.castSucc_x_ne_insertLast_y (x : Cell n) (targetCell : Cell n)
        contradiction
      · case _ castSucc_x_ne_insertLast_targetCell =>
        simp [CoeDep.coe, x_ne_targetCell_insertLast]
        apply Subtype.eq
        simp
        apply Cell.castPred_y_eq_x_of_castSucc_x_eq_y_of_forall_mem_y_ne_last rfl

theorem right_inverse_downward_upward
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.RightInverse (@downward _ split targetCell) (@upward _ split targetCell) := by
    apply Function.LeftInverse.rightInverse_of_surjective
    · apply left_inverse_downward_upward
    · apply upward_surjective

theorem left_inverse_upward_downward
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.LeftInverse (@upward _ split targetCell) (@downward _ split targetCell) := by
    apply Function.RightInverse.leftInverse
    apply right_inverse_downward_upward

theorem right_inverse_upward_downward
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.RightInverse (@upward _ split targetCell) (@downward _ split targetCell) := by
    apply Function.LeftInverse.rightInverse
    apply left_inverse_downward_upward

theorem upward_injective
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Injective (@upward _ split targetCell)
    := Function.LeftInverse.injective (left_inverse_downward_upward targetCell)

theorem upward_bijective
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Bijective (@upward _ split targetCell) := by
    constructor
    · apply upward_injective
    · apply upward_surjective

theorem downward_bijective
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Bijective (@downward _ split targetCell) := by
    apply Function.bijective_iff_has_inverse.mpr
    exists upward
    constructor
    · apply left_inverse_upward_downward
    · apply right_inverse_upward_downward

-- Injectivity, embeddings

def upwardEmbedding
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Embedding split (split.insertLastAt targetCell) :=
    ⟨upward, upward_injective targetCell⟩

def downwardEmbedding
    {n : ℕ}
    {split : Split n}
    (targetCell : split)
  : Function.Embedding (split.insertLastAt targetCell) split :=
    ⟨downward split targetCell, (downward_bijective targetCell).injective⟩

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
