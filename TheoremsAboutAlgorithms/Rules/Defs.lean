import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.Finset.Basic

-- A tag is something we use to connect a `Rule` with an `Instance`. For now we model them as type `Fin` (i.e. there's)
-- a finite number of tags. For example, if our instances are servers and our tags are some kind of stringy label, we
-- could have the following tags `LOCATION_DE, LOCATION_US, GAME_WOW` and the following setup:
--
--    Server:
--      Code: Curie
--      Tags: LOCATION_DE, GAME_WOW
--
--    Server:
--      Code: Cherenkov
--      Tags: LOCATION_US, GAME_WOW
abbrev Tag := Fin
abbrev Tags (n : ℕ) := Finset (Tag n)
