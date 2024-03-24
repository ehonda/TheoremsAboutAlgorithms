import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Fin

namespace Cell

-- TODO: Maybe there's a more elegant way to use all those mapped functions
def cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  := Fin.cast h '' cell

theorem cast_mem_iff {n : ℕ} (cell : Cell n) (x : Fin n)
  : x ∈ cell.cast rfl ↔ x ∈ cell := by simp [cast]

theorem cast_Injective {n m : ℕ} (h : n = m) : Function.Injective (cast h) := by
  apply Set.image_injective.mpr
  exact Fin.cast_injective h

theorem cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (cast h) := by
  apply Set.image_surjective.mpr
  exact Fin.cast_surjective h

theorem cast_bijective {n m : ℕ} (h : n = m) : Function.Bijective (cast h)
  := ⟨cast_Injective h, cast_surjective h⟩

theorem cast_nonempty_iff {n m : ℕ} (h : n = m) (cell : Cell n)
  : (cell.cast h).Nonempty ↔ cell.Nonempty := by simp [cast]

def castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := Fin.castSucc '' cell

--def castPredLambda {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n)
--  := (λ x : {y : Fin (n + 1) // y ∈ cell} ↦ Fin.castPred x.val (h x.val x.property))
--
--theorem cell_eq_subtype {n : ℕ} (cell : Cell n) : Cell n = Set {x : Fin n // x ∈ cell} := by
--  simp [Cell]
--  sorry

-- TODO: How do we remove the sorry?
--def castPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) : Cell n
--  --:= sorry
--  := (castPredLambda cell h) '' (cell_eq_subtype _ ▸ cell)
--  --:= (λ x ↦ Fin.castPred x sorry) '' cell

--def castPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) : Cell n
--  --:= sorry
--  := (λ x ↦ Fin.castPred x (h x _)) '' cell
--  --:= (λ x ↦ Fin.castPred x sorry) '' cell

theorem coe_cell_eq_fin {n : ℕ} (cell : Cell n) : ↑cell = Fin n := by
  
  sorry

def f_restrict {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) (x : cell) : Fin n
  := Fin.castPred x (h x x.property)

def castPredLambda {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last n) : ↑cell → Fin n
  := Set.restrict cell (coe_cell_eq_fin cell ▸ f_restrict cell h)

-- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
theorem castSucc_injective (n : ℕ) : Function.Injective (castSucc (n := n)) := by
  apply Set.image_injective.mpr
  exact Fin.castSucc_injective n

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
  := cell.castSucc.insert (Fin.last n)

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
theorem mem_or_not_mem {n : ℕ} (cell : Cell n) (x : Fin n)
  : x ∈ cell ∨ x ∉ cell :=
    sorry
    --let cell' := Set.toFinset cell
    --sorry

end Cell
