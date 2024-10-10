import TheoremsAboutAlgorithms.Rules.Defs
import TheoremsAboutAlgorithms.Rules.Instance

namespace Rule

inductive Rule (n : ℕ) where
  | positive (tags : Tags n)
  | negative (tags : Tags n)

def appliesTo (n : ℕ) (rule : Rule n) (inst : Instance n) : Prop :=
  match rule with
  | .positive tags => inst.tags ⊆ tags
  | .negative tags => inst.tags ∩ tags = ∅

end Rule
