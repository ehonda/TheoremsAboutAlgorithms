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

-- TODO: There must be an existing definition for this in the libraries. Find it and use it.
def embedFinIntoFinSucc {n : ℕ} (i : Fin n) : Fin (n + 1) := ⟨i.val, (Nat.lt.step i.is_lt)⟩

-- This is essentialy cell ↦ cell ∪ {n}
def transformCell {n : ℕ} (cell : Cell[Fin n]) : Cell[Fin (n + 1)]
  := insert (Fin.ofNat n) (embedFinIntoFinSucc '' cell)

-- TODO: Look for a nicer proof of this.
theorem transformCell_is_disjoint_union {n : ℕ} (cell : Cell[Fin n])
  : Disjoint (embedFinIntoFinSucc '' cell) {Fin.ofNat n} := by
    apply disjoint_iff.mpr
    simp
    intro k _
    rw [embedFinIntoFinSucc, Fin.ofNat]
    simp
    apply lt_or_lt_iff_ne.mp
    have : k.val < n := by simp
    exact Or.inl this

--def f := Fin.succ (4 : Fin 5)
--
--#check f
--
--example : f.val = 5 := by
--  simp [f]
--  rfl
--
--def g := embedFinIntoFinSucc (4 : Fin 5)
--
--#check g
--
--example : g.val = 4 := by
--  simp [g]
--  rfl

--def g (i : Fin n) : Fin (n + 1) := match i with
--  | ⟨i, hi⟩ => ⟨i, (Nat.lt.step hi)⟩
--
--def g' (i : Fin n) : Fin (n + 1) := ⟨i.val, (Nat.lt.step i.is_lt)⟩
--
--def g'' (_ : Fin n) : Fin (n + 1) := ⟨n, Nat.lt.base n⟩

--#print f

--#print Fin.ofNat
--
--def b : ℤ :=
--  let a := (Fin.ofNat 4 : Fin 5)
--  ↑a

-- TODO: How do we allow empty set for the target cell here (which is also why we don't require targetCell ∈ split)
def transformSplit {n : ℕ} (split : Split[Fin n]) (targetCell : Cell[Fin n]) : Split[Fin (n + 1)]
  -- TODO: Find a cleaner way to write this
  := insert (transformCell targetCell) ((λ cell ↦ embedFinIntoFinSucc '' cell) '' (split \ {targetCell}))
