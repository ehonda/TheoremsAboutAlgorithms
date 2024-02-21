import Mathlib.Data.Setoid.Partition
import Init.Data.Fin.Basic

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
notation "Cell[" α "]" => Set α
-- TODO: How can we make it so in Lean infoview, terms of type Split[ℕ] are displayed not displayed as
--       Cell[Cell[ℕ]]?
notation:max "Split[" α "]" => Set (Cell[α])

def IsPartitionOfNatsUpToN {n : ℕ} (split : Split[Fin n]) : Prop
  := Setoid.IsPartition split

def transformCell {n : ℕ} (cell : Cell[Fin n]) : Cell[Fin (n + 1)]
  := Fin.succ '' cell ∪ {Fin.ofNat n}

--def f := Fin.succ (Fin 5)

--def g (i : Fin n) : Fin (n + 1) := match i with
--  | ⟨i, hi⟩ => ⟨i, (Nat.lt.step hi)⟩
--
--def g' (i : Fin n) : Fin (n + 1) := ⟨i.val, (Nat.lt.step i.is_lt)⟩
--
--def g'' (_ : Fin n) : Fin (n + 1) := ⟨n, Nat.lt.base n⟩

--#print f

theorem transformCell_of_partition_is_disjoint_union
    {n : ℕ}
    {cell : Cell[Fin n]}
    (split : Split[Fin n])
    (h_cell : cell ∈ split)
    (h_partition : IsPartitionOfNatsUpToN split)
  : Disjoint (Fin.succ '' cell) {Fin.ofNat n} := by
    apply disjoint_iff.mpr
    sorry

--theorem transformCell_of_partition_is_disjoint_union
--    {split : Split[ℕ]}
--    {n : ℕ}
--    (cell : Cell[ℕ])
--    (h_cell : cell ∈ split)
--    (h_partition : split.IsPartitionOfNatsUpTo n)
--  : cell ∩ {n} = ∅ := by
--    have h_union : ⋃₀ split = Set.Ico 0 n := h_partition.2.2
--    have cell_subset : cell ⊆ Set.Ico 0 n := by
--      sorry
--    sorry
