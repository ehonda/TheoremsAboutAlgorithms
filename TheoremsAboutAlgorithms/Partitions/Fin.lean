import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Function
import Mathlib.Init.Logic

namespace Fin

theorem cast_injective {n m : ℕ} (h : n = m) : Function.Injective (cast h) := by
  intro x y h
  simp [cast] at h
  exact ext h

theorem cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (cast h) := by
  intro x
  exists { val := x.val, isLt := by simp [h, x.is_lt] }

theorem cast_bijective {n m : ℕ} (h : n = m) : Function.Bijective (cast h)
  := ⟨cast_injective h, cast_surjective h⟩

-- TODO: We don't have surjective / bijective for Cell.castSucc as Fin.last has no preimage. We could however prove it
--       for the restriction of Cell.castSucc to cells not containing n, but it's not clea how to best do that.
--
--       For now we use those "exists_preimage_of_ne_last" theorems to show what we need (but there could be better
--       abstractions to use).
theorem castSucc_exists_preimage_of_ne_last {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ last n)
  : ∃! (y : Fin n), y.castSucc = x := by
    have h_x_lt_n : ↑x < n := by sorry
    exists { val := x.val, isLt := h_x_lt_n }
    simp
    intro y hy
    sorry
    --have : castSucc x = { val := x.val, isLt := h_x_lt_n } := by sorry

end Fin
