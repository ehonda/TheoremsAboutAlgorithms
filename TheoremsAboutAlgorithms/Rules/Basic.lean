import TheoremsAboutAlgorithms.Rules.Defs
import TheoremsAboutAlgorithms.Rules.Instance
import Mathlib.Data.Fintype.Basic

namespace Rule

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

abbrev Rules (n : ℕ) := Finset (Rule n)

def appliesTo {n : ℕ} (rule : Rule n) (inst : Instance n) : Prop :=
  match rule with
  | .positive tags => tags ⊆ inst.tags
  | .negative tags => tags ∩ inst.tags = ∅

-- TODO: Better name
def applyTo {n : ℕ} (rules : Rules n) (inst : Instance n) : Prop :=
  -- TODO: Define such that the rules apply if at least one of them applies
  sorry

-- TODO: Is that a good name?
def contrapose {n : ℕ} (rule : Rule n) : Rules n :=
  match rule with
  | .positive tags =>
    let tags' := Finset.univ \ tags
    -- TODO: These two can for sure be written more tersely
    let ctor := λ tag ↦ Rule.negative {tag}
    let ctor_inj : ctor.Injective := by
      simp only [Function.Injective, Rule.negative.injEq, Finset.singleton_inj, imp_self, implies_true]
    Finset.map ⟨ctor, ctor_inj⟩ tags'
  | .negative tags =>
    sorry

-- TODO: Better name
theorem applyTo_contrapose (n : ℕ) (rule : Rule n) (inst : Instance n) :
  applyTo {rule} inst = applyTo (contrapose rule) inst := by
    sorry

end Rule
