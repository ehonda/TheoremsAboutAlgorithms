import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image
import TheoremsAboutAlgorithms.Partitions.Defs
import TheoremsAboutAlgorithms.Partitions.Fin

namespace Cell

-- TODO: Maybe there's a more elegant way to use all those mapped functions
def cast {n m : ℕ} (h : n = m) (cell : Cell n) : Cell m
  := Fin.cast h '' cell

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

-- Fin.castSucc_injective is already a theorem in Mathlib.Data.Fin.Basic
theorem castSucc_injective (n : ℕ) : Function.Injective (castSucc (n := n)) := by
  apply Set.image_injective.mpr
  exact Fin.castSucc_injective n

end Cell
