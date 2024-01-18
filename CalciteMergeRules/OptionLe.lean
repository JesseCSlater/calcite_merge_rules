import Mathlib.Logic.IsEmpty
import Mathlib.Init.Data.Nat.Lemmas

/- I am just using this to be able to extract an element from
   a multiset, by sorting it into a list. However, this is
   quite pointless since I know all values will be the same anyway,
   since I only do this to get the unique group_by values out after
   breaking the table into equivalence classes. This should all be
   removed in a refactor.
-/
abbrev Option.Le : Option ℕ → Option ℕ → Prop
  | some m, some n => m ≤ n
  | none, some _ => False
  | _, _ => True

instance decidableLe : DecidableRel Option.Le := by
  unfold Option.Le
  intro a b
  cases a <;> cases b <;> infer_instance

instance isTransLe : IsTrans (Option ℕ) Option.Le where
  trans := by
    unfold Option.Le
    intro a b c
    cases a <;> cases b <;> cases c <;> simp
    intro h1 h2
    exact Nat.le_trans h1 h2

instance isAntisymmLe : IsAntisymm (Option ℕ) Option.Le where
  antisymm := by
    unfold Option.Le
    intro a b h1 h2
    cases a <;> cases b <;> simp_all
    exact Nat.le_antisymm h1 h2

instance isTotalLe : IsTotal (Option ℕ) Option.Le where
  total := by
    unfold Option.Le
    intro a b
    cases a
    case some v1 =>
      cases b
      case some v2 =>
        exact Nat.le_or_le v1 v2
      case _ => simp
    case _ => simp
