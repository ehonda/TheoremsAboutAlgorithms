import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import TheoremsAboutAlgorithms.Partitions.Fin
import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs

-- WIP (III): Build this in terms of Finset Cells so we get decidable equality on them and can define computable `f` and
--            `g` in WIP (II).

namespace Cell

-- TODO: Define something like Fin.castEmbedding := ⟨Fin.cast, Fin.cast_injective⟩
def cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  := Finset.map (Fin.castEmbedding h) cell

theorem cast_mem_iff {n : ℕ} (cell : Cell n) (x : Fin n)
  : x ∈ cell.cast rfl ↔ x ∈ cell := by simp [cast, Fin.castEmbedding]

theorem cast_injective {n m : ℕ} (h : n = m) : Function.Injective (cast h)
  := Finset.map_injective (Fin.castEmbedding h)

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
  --:= Finset.map ⟨Fin.castSuccEmb, Fin.castSuccEmb.inj⟩ cell
  -- TODO: Use Fin.castSuccEmb for a terse definition
  := Finset.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩ cell

theorem last_not_mem_castSucc {n : ℕ} (cell : Cell n)
  : Fin.last _ ∉ cell.castSucc := by
    simp [castSucc]
    intro x _
    apply lt_or_lt_iff_ne.mp
    left
    exact x.isLt

theorem disjoint_singleton_last_castSucc {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.last n} cell.castSucc := by
    apply disjoint_iff.mpr
    apply Finset.singleton_inter_of_not_mem
    exact last_not_mem_castSucc cell

theorem castSucc_empty_iff {n : ℕ} (cell : Cell n)
  : cell.castSucc = ∅ ↔ cell = ∅ := by simp [castSucc]

-- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
theorem castSucc_injective (n : ℕ) : Function.Injective (@castSucc n)
  := Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective n⟩

-- Useful: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Restrict
def restrictFinCastPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) (x : cell) : Fin n
  -- s := cell, f := Fin.castPred, a := x
  -- We then get `↑x ≠ Fin.last n → Fin n` and therefore provide `(h x x.property)` to get `Fin n`
  -- We don't need to parenthesize the first expression, but we do so for clarity.
  := (Set.restrict cell Fin.castPred x) (h x x.property)

-- Useful: Set.range_restrict
def castPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) : Cell n
  := Finset.image (cell.restrictFinCastPred h) Finset.univ

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
  := Finset.cons (Fin.last n) (cell.castSucc) (last_not_mem_castSucc cell)

theorem last_mem_insertLast {n : ℕ} (cell : Cell n) : Fin.last n ∈ cell.insertLast := by
  simp [insertLast]

-- {Fin.last n} ∪ castSucc x = {Fin.last n} ∪ castSucc y
-- TODO: Move to a Finset file
-- TODO: Naming
-- TODO: This seems to be missing in mathlib, maybe contribute it?
theorem helper
    {α : Type*}
    [DecidableEq α]
    {x : α}
    {s t : Finset α}
    (disjoint_singleton_x_s : Disjoint {x} s)
    (disjoint_singleton_x_t : Disjoint {x} t)
    (eq_union : {x} ∪ s = {x} ∪ t)
  : s = t := by
    ext y
    constructor
    · intro y_mem_s
      cases Decidable.eq_or_ne x y with
        | inl x_eq_y =>
          have y_not_mem_s : y ∉ s := by
            rw [x_eq_y] at disjoint_singleton_x_s
            exact Finset.disjoint_singleton_left.mp disjoint_singleton_x_s
          contradiction
        | inr x_ne_y =>
          have y_mem_singleton_x_union_s : y ∈ {x} ∪ s := by simp [y_mem_s]
          have y_mem_singleton_x_union_t : y ∈ {x} ∪ t := (Finset.ext_iff.mp eq_union y).mp y_mem_singleton_x_union_s
          simp [Finset.mem_union] at y_mem_singleton_x_union_t
          cases y_mem_singleton_x_union_t with
            | inl y_eq_x => have x_eq_y := y_eq_x.symm; contradiction
            | inr y_mem_t => exact y_mem_t
    -- TODO: Can we get rid of this duplicate and totally symmetric subproof? wlog or something?
    · intro y_mem_t
      cases Decidable.eq_or_ne x y with
        | inl x_eq_y =>
          have y_not_mem_t : y ∉ t := by
            rw [x_eq_y] at disjoint_singleton_x_t
            exact Finset.disjoint_singleton_left.mp disjoint_singleton_x_t
          contradiction
        | inr x_ne_y =>
          have y_mem_singleton_x_union_t : y ∈ {x} ∪ t := by simp [y_mem_t]
          have y_mem_singleton_x_union_s : y ∈ {x} ∪ s := (Finset.ext_iff.mp eq_union y).mpr y_mem_singleton_x_union_t
          simp [Finset.mem_union] at y_mem_singleton_x_union_s
          cases y_mem_singleton_x_union_s with
            | inl y_eq_x => have x_eq_y := y_eq_x.symm; contradiction
            | inr y_mem_s => exact y_mem_s

theorem insertLast_injective {n : ℕ} : Function.Injective (@insertLast n) := by
  intro x y h
  simp [insertLast] at h
  have castSucc_x_eq_castSucc_y : x.castSucc = y.castSucc := by
    simp [Finset.insert_eq] at h
    exact helper (disjoint_singleton_last_castSucc x) (disjoint_singleton_last_castSucc y) h
  exact (@castSucc_injective n) castSucc_x_eq_castSucc_y

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
