import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Function
import Mathlib.Init.Logic
import Mathlib.Logic.Embedding.Basic

namespace Fin

-- TODO: These are missing in mathlib, contribute them
theorem cast_injective {n m : ℕ} (h : n = m) : Function.Injective (cast h) := by
  intro x y h
  simp [cast] at h
  exact ext h

theorem cast_surjective {n m : ℕ} (h : n = m) : Function.Surjective (cast h) := by
  intro x
  exists { val := x.val, isLt := by simp [h, x.is_lt] }

theorem cast_bijective {n m : ℕ} (h : n = m) : Function.Bijective (cast h)
  := ⟨cast_injective h, cast_surjective h⟩

-- TODO: Make this an OrderEmbedding: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Hom/Basic.html#OrderEmbedding
def castEmbedding {n m : ℕ} (h : n = m) : Fin n ↪ Fin m :=
  ⟨cast h, cast_injective h⟩

-- TODO: We don't have surjective / bijective for Cell.castSucc as Fin.last has no preimage. We could however prove it
--       for the restriction of Cell.castSucc to cells not containing n, but it's not clea how to best do that.
--
--       For now we use those "exists_preimage_of_ne_last" theorems to show what we need (but there could be better
--       abstractions to use).
--
-- TODO: This seems pretty involved, maybe there's an easier way to do this?
theorem castSucc_exists_preimage_of_ne_last {n : ℕ} {x : Fin (n + 1)} (hx : x ≠ last n)
  : ∃! (y : Fin n), y.castSucc = x := by
    have h_x_lt_n : ↑x < n := val_lt_last hx
    exists { val := x.val, isLt := h_x_lt_n }
    simp
    intro y hy
    simp [castSucc, castAdd, castLE] at hy
    apply (eq_mk_iff_val_eq (a := y) (hk := h_x_lt_n)).mpr
    rw [← hy]

end Fin
