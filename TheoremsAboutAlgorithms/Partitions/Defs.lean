import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.Set

-- Terminology:
--   * For any n : ℕ, a Cell n is a set of Fin n, i.e. a subset of the base set {0, 1, ..., n - 1}.
--   * For any n : ℕ, a Split n is a set of Cell n, i.e. a collection of subsets of the base set {0, 1, ..., n - 1}.
--     Note that these don't have to be disjoint, so this is not the same as a partition of the base set.
--
-- By using Fin n to represent the base set, we can use the definition Setoid.IsPartition from the standard library
-- to talk about partitions, which seems to present a nicer api than the one we would get by using Set ℕ and using
-- the classical definition of a partition, like e.g. the definition on wikipedia:
--
--    https://en.wikipedia.org/wiki/Partition_of_a_set#Definition_and_notation
abbrev Cell (n : ℕ) := Set (Fin n)
abbrev Split (n : ℕ) := Set (Cell n)
