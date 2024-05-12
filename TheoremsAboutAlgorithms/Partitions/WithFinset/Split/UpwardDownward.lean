import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs
import TheoremsAboutAlgorithms.Partitions.WithFinset.Split.Basic

namespace Split

-- TODO: Group theorems below in anonymous sections where we can then also e.g. set `split`, `targetCell` etc once all
--       theorems in the section use them.
variable {n : ℕ}

------------------------------------------------------------------------------------------------------------------------
--                          Embeddings between split and split.insertLastAt targetCell                                --
------------------------------------------------------------------------------------------------------------------------

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
--    * Theorem names and naming in general in this section are lacking, improve them!

-- TODO: Make this a section and define all the common implicit arguments (`n, split, targetCell`) at the top
theorem insertLast_mem_insertLastAt_of_eq
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
    {split : Split n}
    {targetCell : Cell n}
    {cell : split}
    (cell_ne_targetCell : ↑cell ≠ targetCell)
  : CoeDep (Cell (n + 1)) (Cell.castSucc cell) (split.insertLastAt targetCell) where
    coe := by
      use Cell.castSucc cell
      exact castSucc_mem_insertLastAt_of_ne cell_ne_targetCell

def upward
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
    {split : Split n}
    {targetCell : Cell n}
    {cell : split.insertLastAt targetCell}
    (cell_ne_targetCell_insertLast : ↑cell ≠ targetCell.insertLast)
  : ∀ x ∈ (cell : Cell (n + 1)), ↑x ≠ Fin.last n := by
    intro x x_mem_cell
    exact ne_last_of_ne_insertLast_of_mem cell_ne_targetCell_insertLast ⟨x, x_mem_cell⟩

theorem mem_castSucc_of_ne_targetCell_of_mem_castSucc_erase_targetCell
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
    (split : Split n)
    (targetCell : split)
    (cell : split.insertLastAt targetCell)
  : split :=
    if h : cell = Cell.insertLast (targetCell : Cell n)
    then targetCell
    else (CoeDepCastPredOfNeInsertLast h).coe

theorem castPred_x_mem_split_of_mem_split_of_castSucc_eq
    {split : Split n}
    {x' : Cell n}
    {x : Cell (n + 1)}
    (x'_mem_split : x' ∈ split)
    (castSucc_x'_eq_x : Cell.castSucc x' = x)
    -- TODO: Better api for the precondition, maybe as a predicate?
    (castPred_x_preCond : ∀ f ∈ x, f ≠ Fin.last _ := by simp)
  : Cell.castPred x castPred_x_preCond ∈ split := by
    subst x
    simp [Cell.castPred_castSucc_eq]
    exact x'_mem_split

-- Surjectivity
theorem upward_surjective
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
          have x_val_mem_insertLastAt := x.property
          simp [insertLastAt, x_val_ne_insertLast_targetCell, castSucc, Cell.castSuccEmbedding]
            at x_val_mem_insertLastAt
          obtain ⟨_, x', x'_mem_split, castSucc_x'_eq_x_val⟩ := x_val_mem_insertLastAt
          exact castPred_x_mem_split_of_mem_split_of_castSucc_eq x'_mem_split castSucc_x'_eq_x_val _
        exists castPred_x_val_mem_split
        split
        · case _ castPred_x_val_eq_targetCell_val =>
          have x_val_mem_insertLastAt := x.property
          simp [insertLastAt, x_val_ne_insertLast_targetCell, castSucc, Cell.castSuccEmbedding]
            at x_val_mem_insertLastAt
          obtain ⟨x_val_ne_castSucc_targetCell, _⟩ := x_val_mem_insertLastAt
          have := Cell.eq_castSucc_of_castPred_eq _ castPred_x_val_eq_targetCell_val
          contradiction
        · case _ castPred_x_val_ne_insertLast_targetCell =>
          simp [CoeDep.coe]
          apply Subtype.eq
          simp [Cell.castSucc_castPred_eq]

-- Inverses

theorem left_inverse_downward_upward
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
    {split : Split n}
    (targetCell : split)
  : Function.RightInverse (@downward _ split targetCell) (@upward _ split targetCell) := by
    apply Function.LeftInverse.rightInverse_of_surjective
    · apply left_inverse_downward_upward
    · apply upward_surjective

theorem left_inverse_upward_downward
    {split : Split n}
    (targetCell : split)
  : Function.LeftInverse (@upward _ split targetCell) (@downward _ split targetCell) := by
    apply Function.RightInverse.leftInverse
    apply right_inverse_downward_upward

theorem right_inverse_upward_downward
    {split : Split n}
    (targetCell : split)
  : Function.RightInverse (@upward _ split targetCell) (@downward _ split targetCell) := by
    apply Function.LeftInverse.rightInverse
    apply left_inverse_downward_upward

theorem upward_injective
    {split : Split n}
    (targetCell : split)
  : Function.Injective (@upward _ split targetCell)
    := Function.LeftInverse.injective (left_inverse_downward_upward targetCell)

theorem upward_bijective
    {split : Split n}
    (targetCell : split)
  : Function.Bijective (@upward _ split targetCell) := by
    constructor
    · apply upward_injective
    · apply upward_surjective

theorem downward_bijective
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
    {split : Split n}
    (targetCell : split)
  : Function.Embedding split (split.insertLastAt targetCell) :=
    ⟨upward, upward_injective targetCell⟩

def downwardEmbedding
    {split : Split n}
    (targetCell : split)
  : Function.Embedding (split.insertLastAt targetCell) split :=
    ⟨downward split targetCell, (downward_bijective targetCell).injective⟩

end Split
