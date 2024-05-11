import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import TheoremsAboutAlgorithms.Partitions.Fin
import TheoremsAboutAlgorithms.Partitions.WithFinset.Defs
import TheoremsAboutAlgorithms.Partitions.WithFinset.Finset

-- WIP (III): Build this in terms of Finset Cells so we get decidable equality on them and can define computable `f` and
--            `g` in WIP (II).

namespace Cell

-- TODO: Define something like Fin.castEmbedding := ⟨Fin.cast, Fin.cast_injective⟩
def cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  := Finset.map (Fin.castEmbedding h) cell

def castEmbedding {n m : ℕ} (h : n = m) : Cell n ↪ Cell m
  := ⟨cast h, Finset.map_injective (Fin.castEmbedding h)⟩

theorem mem_cast_iff_mem {n : ℕ} (cell : Cell n) (x : Fin n)
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

theorem cast_nonempty_iff_nonempty {n m : ℕ} (h : n = m) (cell : Cell n)
  : (cell.cast h).Nonempty ↔ cell.Nonempty := by simp [cast]

def castSucc {n : ℕ} (cell : Cell n) : Cell (n + 1)
  --:= Finset.map ⟨Fin.castSuccEmb, Fin.castSuccEmb.inj⟩ cell
  -- TODO: Use Fin.castSuccEmb for a terse definition
  := Finset.map ⟨Fin.castSucc, Fin.castSucc_injective n⟩ cell

def castSuccEmbedding {n : ℕ} : Cell n ↪ Cell (n + 1)
  := ⟨castSucc, Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective n⟩⟩

theorem last_not_mem_castSucc {n : ℕ} (cell : Cell n)
  : Fin.last _ ∉ cell.castSucc := by
    simp [castSucc]
    intro x _
    apply lt_or_lt_iff_ne.mp
    left
    exact x.isLt

theorem disjoint_singleton_last_castSucc {n : ℕ} (cell : Cell n)
  : Disjoint {Fin.last _} cell.castSucc := by
    apply disjoint_iff.mpr
    apply Finset.singleton_inter_of_not_mem
    exact last_not_mem_castSucc cell

theorem castSucc_empty_iff {n : ℕ} (cell : Cell n)
  : cell.castSucc = ∅ ↔ cell = ∅ := by simp [castSucc]

-- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
theorem castSucc_injective (n : ℕ) : Function.Injective (@castSucc n)
  := Finset.map_injective ⟨Fin.castSucc, Fin.castSucc_injective _⟩

-- Useful: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Function.html#Restrict
def restrictFinCastPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _) (x : cell) : Fin n
  -- s := cell, f := Fin.castPred, a := x
  -- We then get `↑x ≠ Fin.last n → Fin n` and therefore provide `(h x x.property)` to get `Fin n`
  -- We don't need to parenthesize the first expression, but we do so for clarity.
  := (Set.restrict cell Fin.castPred x) (h x x.property)

-- Function.Injective (restrictFinCastPred cell h)
theorem restrictFinCastPred_injective {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _)
  : Function.Injective (restrictFinCastPred cell h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictFinCastPred, Set.restrict] at castPred_x_eq_castPred_y
    apply Subtype.eq
    exact Fin.castPred_inj.mp castPred_x_eq_castPred_y

def castPred {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _) : Cell n
  := Finset.map ⟨cell.restrictFinCastPred h, restrictFinCastPred_injective cell h⟩ Finset.univ

theorem castPred_y_eq_x_of_castSucc_x_eq_y_of_forall_mem_y_ne_last
    {n : ℕ}
    {x : Cell n}
    {y : Cell (n + 1)}
    (castSuc_x_eq_y : x.castSucc = y)
    (forall_mem_y_ne_last : ∀ f ∈ y, f ≠ Fin.last _)
  : Cell.castPred y forall_mem_y_ne_last = x := by
    -- See https://proofassistants.stackexchange.com/a/1063 for why we use `subst` here
    subst y
    ext f
    simp [castSucc, castPred]
    unfold restrictFinCastPred
    simp [Set.restrict]
    constructor
    · intro cast_cast
      obtain ⟨g, g_spec, castPred_g_eq_f⟩ := cast_cast
      obtain ⟨_, h_spec, _⟩ := g_spec
      subst g
      simp [Fin.castPred_castSucc] at castPred_g_eq_f
      rw [← castPred_g_eq_f]
      exact h_spec
    · intro cast_cast
      exists f.castSucc
      constructor
      · exact Fin.castPred_castSucc
      · exists f

-- TODO: Naming
-- TODO: Maybe this should be in Fin namespace?
theorem castPred_mem_of_mem_castSucc_of_ne_last
    {n : ℕ}
    {cell : Cell n}
    {x : Fin (n + 1)}
    (x_mem_castSucc_cell : x ∈ cell.castSucc)
    (x_ne_last : x ≠ Fin.last _)
  : x.castPred x_ne_last ∈ cell := by
    simp [castSucc, Fin.castSucc, Fin.castAdd, Fin.castLE] at x_mem_castSucc_cell
    obtain ⟨y, y_mem_cell, y_def⟩ := x_mem_castSucc_cell
    simp [← y_def, y_mem_cell]

theorem castSucc_castPred_eq {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _)
  : (cell.castPred h).castSucc = cell := by
    ext f
    simp [castSucc, castPred]
    constructor
    · intro h
      obtain ⟨g, ⟨f', f'_mem_cell, restrictFinCastPred_cell_f'_eq_g⟩, castPred_g_eq_f⟩ := h
      rw [restrictFinCastPred, Set.restrict] at restrictFinCastPred_cell_f'_eq_g
      rw [← castPred_g_eq_f, ← restrictFinCastPred_cell_f'_eq_g]
      simp
      exact f'_mem_cell
    · intro f_mem_cell
      exists f.castPred (h _ f_mem_cell)
      constructor
      · exists f
        exists f_mem_cell
      · simp

theorem castPred_castSucc_eq
    {n : ℕ}
    (cell : Cell n)
    (castPred_castSucc_cell_preCond : ∀ f ∈ cell.castSucc, f ≠ Fin.last _ := sorry)
  : cell.castSucc.castPred castPred_castSucc_cell_preCond = cell := by
    ext f
    simp [castSucc, castPred]
    constructor
    · intro h
      obtain ⟨g, ⟨f', f'_mem_cell, restrictFinCastPred_cell_f'_eq_g⟩, castPred_g_eq_f⟩ := h
      rw [restrictFinCastPred, Set.restrict] at restrictFinCastPred_cell_f'_eq_g
      rw [← castPred_g_eq_f, ← restrictFinCastPred_cell_f'_eq_g]
      simp
      exact f'_mem_cell
    · intro f_mem_cell
      exists f.castSucc
      constructor
      · exists f
        exists f_mem_cell
      · simp

-- This is essentially cell ↦ {n} ∪ cell
def insertLast {n : ℕ} (cell : Cell n) : Cell (n + 1)
  := Finset.cons (Fin.last _) (cell.castSucc) (last_not_mem_castSucc cell)

theorem last_mem_insertLast {n : ℕ} (cell : Cell n) : Fin.last _ ∈ cell.insertLast := by
  simp [insertLast]

theorem insertLast_injective {n : ℕ} : Function.Injective (@insertLast n) := by
  intro x y h
  simp [insertLast] at h
  apply castSucc_injective
  apply Finset.eq_of_disjoint_singleton_of_disjoint_singleton_of_eq_unions
  · exact disjoint_singleton_last_castSucc x
  · exact disjoint_singleton_last_castSucc y
  · exact h

theorem insertLast_nonempty {n : ℕ} (cell : Cell n) : cell.insertLast.Nonempty
  := by simp [insertLast]

theorem castSucc_x_ne_insertLast_y
    {n : ℕ}
    (x y : Cell n)
  : x.castSucc ≠ y.insertLast := by
    intro castSucc_x_eq_insertLast_y
    apply last_not_mem_castSucc x
    rw [castSucc_x_eq_insertLast_y]
    exact last_mem_insertLast y

end Cell
