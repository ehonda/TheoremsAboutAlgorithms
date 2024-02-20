import Mathlib.Data.Finset.Basic

-- TODO: Adhere to naming conventions specified in: https://leanprover-community.github.io/contribute/naming.html

------------------------------------------------------------------------------------------------------------------------
--                                                  Definitions                                                       --
------------------------------------------------------------------------------------------------------------------------

universe u

-- Terminology:
--   * A cell of a type α is a subset of α
--   * A split of a type α is a collection of cells of α.
--   * A partition of a type α is a split of α such that the cells are pairwise disjoint and non-empty and their union
--     is the base set.
notation "Cell[" α "]" => Finset α
-- TODO: How can we make it so in Lean infoview, terms of type Split[ℕ] are displayed not displayed as
--       Cell[Cell[ℕ]]?
notation:max "Split[" α "]" => Finset (Finset α)

def CellsArePairwiseDisjoint {α : Type u} [DecidableEq α] (split : Split[α])
  : Prop := ∀ x ∈ split, ∀ y ∈ split, x ≠ y → Disjoint x y

def CellsAreNonEmpty {α : Type u} (split : Split[α])
  : Prop := ∀ x ∈ split, x.Nonempty

-- PROBLEM: We don't have sUnion for Finset

---- TODO: Define type alias for Set (Set α)
--def isPartitionOf (baseSet : Cell[α]) (split : Split[α]) : Prop :=
--    CellsArePairwiseDisjoint split ∧ cellsAreNonEmpty ∧ unionOfSplitIsBaseSet
--  where
--    cellsAreNonEmpty := ∀ x ∈ split, x ≠ ∅
--    unionOfSplitIsBaseSet := ⋃₀ split = baseSet
