import Mathlib.Data.Setoid.Partition
import Init.Data.Fin.Basic

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

------------------------------------------------------------------------------------------------------------------------
--                                                  Definitions                                                       --
------------------------------------------------------------------------------------------------------------------------

-- TODO: Is notation really the right way to go here? It has the following disadvantages:
--          * In lean infoview, terms of type Split[ℕ] are displayed as Cell[Cell[ℕ]].
--          * We can't use dot notation for Split and Cell, e.g. cell.castSucc instead of Cell.castSucc cell.
--       Find a better way to define these types.

-- TODO: Is it better to use insert or the mathematical notation for set union using a singleton set (also for sdiff)?

-- TODO: Add comments everywhere (and especially to theorems).

-- Terminology:
--   * A cell of a type α is a subset of α
--   * A split of a type α is a collection of cells of α.
--   * A partition of a type α is a split of α such that the cells are pairwise disjoint and non-empty and their union
--     is the base set.
notation "Cell[" α "]" => Set α
notation:max "Split[" α "]" => Set (Cell[α])


def Cell.castSucc {n : ℕ} (cell : Cell[Fin n]) : Cell[Fin (n + 1)]
  := Fin.castSucc '' cell

-- This is essentially cell ↦ {n} ∪ cell
def transformCell {n : ℕ} (cell : Cell[Fin n]) : Cell[Fin (n + 1)]
  := (Cell.castSucc cell).insert (Fin.ofNat n)

-- TODO: Look for a nicer proof of this.
theorem transformCell_is_disjoint_insert {n : ℕ} (cell : Cell[Fin n])
  : Disjoint {Fin.ofNat n} (Cell.castSucc cell) := by
    apply disjoint_iff.mpr
    simp [Cell.castSucc, Fin.castSucc, Fin.ofNat]
    intro k _
    apply lt_or_lt_iff_ne.mp
    have : k < n := by simp
    exact Or.inl this

def Split.castSucc {n : ℕ} (split : Split[Fin n]) : Split[Fin (n + 1)]
  := Cell.castSucc '' split

def Split.removeCellAndCastSucc {n : ℕ} (split : Split[Fin n]) (cell : Cell[Fin n]) : Split[Fin (n + 1)]
  := Split.castSucc (split \ singleton cell)

-- We don't require targetCell ∈ split, because we want to be able to have ∅ as a target cell as well.
-- This is essentially split ↦ {transformCell targetCell} ∪ (split \ {targetCell})
def transformSplit {n : ℕ} (split : Split[Fin n]) (targetCell : Cell[Fin n]) : Split[Fin (n + 1)]
  := (Split.removeCellAndCastSucc split targetCell).insert (transformCell targetCell)

theorem transformSplit_is_disjoint_insert {n : ℕ} (split : Split[Fin n]) (targetCell : Cell[Fin n])
  : Disjoint {transformCell targetCell} (Split.removeCellAndCastSucc split targetCell) := by
    apply disjoint_iff.mpr
    simp [Split.removeCellAndCastSucc, Fin.castSucc, Split.castSucc]
    intro cell _ _
    have h_k : ¬ (∀ (x : Fin (n + 1)), x ∈ Cell.castSucc cell ↔ x ∈ transformCell targetCell) := by
      simp [not_iff]
      exists (Fin.ofNat n)
      constructor
      · intro
        simp [transformCell]
        exact Set.mem_insert _ _
      · intro
        apply Set.disjoint_singleton_left.mp
        exact transformCell_is_disjoint_insert cell
    have := Set.ext_iff (s := Cell.castSucc cell) (t := transformCell targetCell)
    exact (not_congr this).mpr h_k

def Split.IsPartition {n : ℕ} (split : Split[Fin n]) : Prop
  := Setoid.IsPartition split
