import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import TheoremsAboutAlgorithms.Partitions.Fin
import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs

-- WIP (III): Build this in terms of Finset Cells so we get decidable equality on them and can define computable `f` and
--            `g` in WIP (II).

namespace Cell

def cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  -- TODO: Maybe we should rather use Finset.map here?
  := Finset.image (Fin.cast h) cell

theorem cast_mem_iff {n : ℕ} (cell : Cell n) (x : Fin n)
  : x ∈ cell.cast rfl ↔ x ∈ cell := by simp [cast]

theorem cast_Injective {n m : ℕ} (h : n = m) : Function.Injective (cast h) := by
  apply Finset.image_injective
  exact Fin.cast_injective h

-- TODO: Maybe later, we don't actually use those
--theorem cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (cast h) := by
--  simp [Function.Surjective]
--  intro y
--  have := (Fin.cast_surjective h) y
--  obtain ⟨x, hx⟩ := this y
--
--theorem cast_bijective {n m : ℕ} (h : n = m) : Function.Bijective (cast h)
--  := ⟨cast_Injective h, cast_surjective h⟩

theorem cast_nonempty_iff {n m : ℕ} (h : n = m) (cell : Cell n)
  : (cell.cast h).Nonempty ↔ cell.Nonempty := by simp [cast]

def castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := Finset.image Fin.castSucc cell

theorem disjoint_singleton_last_castSucc {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.last n} cell.castSucc := by
    apply disjoint_iff.mpr
    simp [castSucc, Fin.castSucc]
    apply Set.inter_nonempty.mpr
    sorry
    --intro k _
    --apply lt_or_lt_iff_ne.mp
    --have : k < n := by simp
    --exact Or.inl this

theorem castSucc_empty_iff {n : ℕ} (cell : Cell n)
  : cell.castSucc = ∅ ↔ cell = ∅ := by simp [castSucc]

-- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
theorem castSucc_injective (n : ℕ) : Function.Injective (castSucc (n := n)) := by
  apply Finset.image_injective
  exact Fin.castSucc_injective n

-- Useful: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Restrict
def restrictFinCastPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) (x : cell) : Fin n
  -- s := cell, f := Fin.castPred, a := x
  -- We then get `↑x ≠ Fin.last n → Fin n` and therefore provide `(h x x.property)` to get `Fin n`
  -- We don't need to parenthesize the first expression, but we do so for clarity.
  := (Set.restrict cell Fin.castPred x) (h x x.property)

-- Useful: Set.range_restrict
def castPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) : Cell n
  := Finset.range (cell.restrictFinCastPred h)

-- TODO: Naming
-- TODO: Maybe this should be in Fin namespace?
theorem castPred_mem_of_mem_castSucc_of_ne_last
    {n : ℕ}
    {cell : Cell n}
    {x : Fin (n + 1)}
    (x_mem_castSucc_cell : x ∈ cell.castSucc)
    (x_ne_last : x ≠ Fin.last n)
  : x.castPred x_ne_last ∈ cell := by
    simp [castSucc, Fin.castSucc, Fin.castAdd, Fin.castLE] at x_mem_castSucc_cell
    obtain ⟨y, y_mem_cell, y_def⟩ := x_mem_castSucc_cell
    simp [← y_def, y_mem_cell]

-- This is essentially cell ↦ {n} ∪ cell
def insertLast {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := insert (Fin.last n) (cell.castSucc)

theorem last_mem_insertLast {n : ℕ} (cell : Cell n) : Fin.last n ∈ cell.insertLast := by
  simp [insertLast]

-- TODO
theorem insertLast_injective {n : ℕ} : Function.Injective (insertLast (n := n)) := by
  intro x y h
  simp [insertLast] at h
  repeat rw [Set.insert_eq] at h
  have castSucc_x_eq_castSucc_y : x.castSucc = y.castSucc := by
    apply Set.eq_of_subset_of_subset
    -- TODO: Remove the duplication, wlog it
    · have : castSucc x ⊆ {Fin.last _} ∪ castSucc y := by
        exact HasSubset.subset.trans_eq (Set.subset_union_right _ _) h
      exact Disjoint.subset_right_of_subset_union this (disjoint_singleton_last_castSucc x).symm
    · have : castSucc y ⊆ {Fin.last _} ∪ castSucc x := by
        exact HasSubset.subset.trans_eq (Set.subset_union_right _ _) h.symm
      exact Disjoint.subset_right_of_subset_union this (disjoint_singleton_last_castSucc y).symm
  exact (castSucc_injective (n := n)) castSucc_x_eq_castSucc_y

theorem insertLast_nonempty {n : ℕ} (cell : Cell n) : cell.insertLast.Nonempty
  := Set.insert_nonempty _ _

-- TODO: Look for a nicer proof of this.
theorem insertLast_is_disjoint_insert {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.last n} cell.castSucc := by
    apply disjoint_iff.mpr
    simp [castSucc, Fin.castSucc]
    intro k _
    apply lt_or_lt_iff_ne.mp
    have : k < n := by simp
    exact Or.inl this

-- TODO: Maybe use Set.mem_toFinset
-- TODO: Do we actually use this somewhere? Can we get rid of it in favor of a constructive proof?
theorem mem_or_not_mem {n : ℕ} (cell : Cell n) (x : Fin n)
  : x ∈ cell ∨ x ∉ cell :=
    sorry
    --let cell' := Set.toFinset cell
    --sorry

-- Demo that we have a decidable equality
example {n : ℕ} (cell cell' : Cell n) : Bool := if cell = cell' then true else false

end Cell
