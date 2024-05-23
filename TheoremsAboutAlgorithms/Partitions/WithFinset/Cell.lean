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
  -- TODO: Can we use `Subtype.restrict` here? (And do we want to?)
  := (Set.restrict cell Fin.castPred x) (h x x.property)

-- Function.Injective (restrictFinCastPred cell h)
theorem restrictFinCastPred_injective {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _)
  : Function.Injective (restrictFinCastPred cell h) := by
    intro x y castPred_x_eq_castPred_y
    simp [restrictFinCastPred, Set.restrict] at castPred_x_eq_castPred_y
    apply Subtype.eq
    exact Fin.castPred_inj.mp castPred_x_eq_castPred_y

-- def restrictFinCastPredEmbedding {n : ℕ} (cell : Cell (n + 1)) (h : ∀ x ∈ cell, x ≠ Fin.last _)
--   : cell ↪ Fin n
--   := ⟨restrictFinCastPred cell h, restrictFinCastPred_injective cell h⟩

def CastPredPrecondition {n : ℕ} (cell : Cell (n + 1)) := ∀ x ∈ cell, x ≠ Fin.last _

def castPred {n : ℕ} (cell : Cell (n + 1)) (h : CastPredPrecondition cell) : Cell n
  := Finset.map ⟨cell.restrictFinCastPred h, restrictFinCastPred_injective cell h⟩ Finset.univ

-- TODO: Messy proof, for sure we can improve it
theorem Cell.castPred_inj {n : ℕ} (x y : Cell (n + 1)) (hx : CastPredPrecondition x) (hy : CastPredPrecondition y)
  : x.castPred hx = y.castPred hy ↔ x = y := by
    constructor
    · intro castPred_x_eq_castPred_y
      ext f
      constructor
      · intro f_mem_x
        apply Decidable.byContradiction
        intro f_not_mem_y
        set f' := f.castPred (hx f f_mem_x) with f'_def
        have f'_mem_castPred_x : f' ∈ x.castPred hx := by
          simp [f'_def, castPred]
          exact ⟨f, f_mem_x, rfl⟩
        have f'_mem_castPred_y : f' ∈ y.castPred hy := by
          rw [← castPred_x_eq_castPred_y]
          exact f'_mem_castPred_x
        have f_mem_y : f ∈ y := by
          simp [castPred] at f'_mem_castPred_y
          obtain ⟨f'', f''_mem_y, f''_def⟩ := f'_mem_castPred_y
          simp [restrictFinCastPred, Set.restrict] at f''_def
          have : f'' = f := by
            apply Fin.castPred_inj.mp
            exact f''_def
          rw [← this]
          exact f''_mem_y
        contradiction
      -- TODO: Remove this duplication by factoring out into a helper lemma or something
      · intro f_mem_y
        apply Decidable.byContradiction
        intro f_not_mem_x
        set f' := f.castPred (hy f f_mem_y) with f'_def
        have f'_mem_castPred_y : f' ∈ y.castPred hy := by
          simp [f'_def, castPred]
          exact ⟨f, f_mem_y, rfl⟩
        have f'_mem_castPred_x : f' ∈ x.castPred hx := by
          rw [castPred_x_eq_castPred_y]
          exact f'_mem_castPred_y
        have f_mem_x : f ∈ x := by
          simp [castPred] at f'_mem_castPred_x
          obtain ⟨f'', f''_mem_x, f''_def⟩ := f'_mem_castPred_x
          simp [restrictFinCastPred, Set.restrict] at f''_def
          have : f'' = f := by
            apply Fin.castPred_inj.mp
            exact f''_def
          rw [← this]
          exact f''_mem_x
        contradiction
    · intro; subst x; rfl

-- -- TODO: Finish this
-- def castPredEmbedding
--     {n : ℕ}
--     (cell : Cell (n + 1))
--     (h : @CastPredPrecondition n)
--   : Cell (n + 1) ↪ Cell n
--   := ⟨cell.castPred h, Finset.map_injective ⟨cell.restrictFinCastPred h, restrictFinCastPred_injective cell h⟩⟩

-- We need this very technical setup for the following reasons:
--
--    1. We want to define `Split.castPred` via `Finset.map` and for that we need `Cell.castPredEmbedding`
--    2. However, `Cell.castPred` is only truly an embedding if we restrict to cells that don't contain `Fin.last _`
--    3. We therefore need a type to represent cells that don't contain `Fin.last _` so we can restrict to it
--
-- We first restrict `Fin.castPred` (to get `Cell.castPRed`), and then we do the analogue for `Cell.castPred`. But we do
-- it in `Split`.

-- TODO: This is all really awkward and hard to get right (though there is something that does make sense to write down)
--       Do we really need it?
-- -- TODO: Naming, where should we put this, do we need this or can we do without?
-- structure CellWithoutLast (n : ℕ) where
--   toCell : Cell (n + 1)
--   forall_mem_ne_last : ∀ x ∈ toCell, x ≠ Fin.last _

-- instance {n : ℕ} : Coe (CellWithoutLast n) (Cell (n + 1)) := ⟨CellWithoutLast.toCell⟩

-- -- instance {n : ℕ} : DecidableEq (CellWithoutLast n) := sorry

-- def restrictFinCastPredEmbedding {n : ℕ} (cell : CellWithoutLast n) : cell.toCell ↪ Fin n
--   := ⟨cell.toCell.restrictFinCastPred cell.forall_mem_ne_last, restrictFinCastPred_injective cell.toCell cell.forall_mem_ne_last⟩

-- def castPred' {n : ℕ} (cell : CellWithoutLast n) : Cell n
--   := Finset.map (restrictFinCastPredEmbedding cell) Finset.univ

-- def castPred'_injective {n : ℕ} : Function.Injective (@castPred' n) := by
--   intro x y h
--   have : x.toCell = y.toCell := by
--     apply Decidable.byContradiction
--     intro toCell_ne
--     sorry
--   have : x = ⟨y.toCell, y.forall_mem_ne_last⟩ := by
--     sorry
--   simp [this]

-- -- TODO: Finish this
-- def castPred_injective {n : ℕ}
--   : Function.Injective (@castPred n _ _) := Finset.map_injective ⟨cell.restrictFinCastPred h, restrictFinCastPred_injective cell h⟩

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

-- TODO: Naming
-- TODO: Maybe this should be in Fin namespace?
theorem mem_castSucc_of_ne_last_of_castPred_mem
    {n : ℕ}
    {cell : Cell n}
    {x : Fin (n + 1)}
    (x_ne_last : x ≠ Fin.last _)
    (castPred_x_mem_cell : x.castPred x_ne_last ∈ cell)
  : x ∈ cell.castSucc := by
    simp [castSucc, Fin.castSucc, Fin.castAdd, Fin.castLE]
    exists x.castPred x_ne_last

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

-- TODO: Add @simp (and research for which theorems we should add it and why)
theorem castPred_castSucc_eq
    {n : ℕ}
    (cell : Cell n)
    (castPred_castSucc_cell_preCond : ∀ f ∈ cell.castSucc, f ≠ Fin.last _ := by simp)
  : cell.castSucc.castPred castPred_castSucc_cell_preCond = cell := by
    ext f
    simp [castSucc, castPred]
    constructor
    · intro h
      obtain ⟨g, ⟨g', g'_mem_cell, castSucc_g'_eq_g⟩, restrictFinCastPred_g_eq_f⟩ := h
      simp [restrictFinCastPred, Set.restrict] at restrictFinCastPred_g_eq_f
      subst g
      simp [Fin.castPred_castSucc] at restrictFinCastPred_g_eq_f
      rw [← restrictFinCastPred_g_eq_f]
      exact g'_mem_cell
    · intro f_mem_cell
      exists f.castSucc
      constructor
      · simp [restrictFinCastPred, Set.restrict]
      · exists f

theorem eq_castSucc_of_castPred_eq
    {n : ℕ}
    {x : Cell (n + 1)}
    {y : Cell n}
    (castPred_x_preCond : ∀ f ∈ x, f ≠ Fin.last _)
    (castPred_x_eq_y : x.castPred castPred_x_preCond = y)
  : x = y.castSucc := by
    ext f
    simp [castSucc] at *
    constructor
    · intro f_mem_x
      exists f.castPred (castPred_x_preCond f f_mem_x)
      constructor
      · rw [← castPred_x_eq_y]
        simp [castPred]
        exists f
        exists f_mem_x
      · simp
    · intro exists_castSucc_eq_f
      obtain ⟨g, g_mem_y, castSucc_g_eq_f⟩ := exists_castSucc_eq_f
      rw [← castPred_x_eq_y] at g_mem_y
      simp [castPred] at g_mem_y
      obtain ⟨g', g'_mem_x, castPred_g'_eq_g⟩ := g_mem_y
      simp [restrictFinCastPred, Set.restrict] at castPred_g'_eq_g
      rw [← castPred_g'_eq_g] at castSucc_g_eq_f
      simp at castSucc_g_eq_f
      rw [← castSucc_g_eq_f]
      exact g'_mem_x

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
