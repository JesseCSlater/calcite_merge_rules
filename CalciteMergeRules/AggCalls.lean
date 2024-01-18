import Mathlib.Data.Multiset.Fold

inductive AggCall
  | COUNT
  | SUM
  | SUM0
  | MIN
  | MAX

instance mergeComm (op : α → α → α) [comm : IsCommutative α op]
  : IsCommutative (Option α) (Option.merge op) where
  comm := by
    intro a b
    unfold Option.merge
    cases a <;> cases b <;> simp
    apply comm.comm

instance mergeAssoc (op : α → α → α) [assoc : IsAssociative α op]
  : IsAssociative (Option α) (Option.merge op) where
  assoc := by
    intro a b c
    unfold Option.merge
    cases a <;> cases b <;> cases c <;> simp
    apply assoc.assoc

instance addComm : IsCommutative (ℕ) (Nat.add) where
  comm := Nat.add_comm

instance addAssoc : IsAssociative (ℕ) (Nat.add) where
  assoc := Nat.add_assoc

def AggCall.call : AggCall → Multiset (Option ℕ) → Option ℕ
  | COUNT => some ∘ Multiset.sizeOf
  | SUM => Multiset.fold (Option.merge Nat.add) none
  | SUM0 => Multiset.fold (Option.merge Nat.add) (some 0)
  | MIN => Multiset.fold (Option.merge min) none
  | MAX => Multiset.fold (Option.merge max) (some 0)

def AggCall.merge : AggCall → AggCall → Option AggCall
  | SUM0, COUNT => COUNT
  | SUM, SUM => SUM
  | SUM0, SUM0 => SUM0
  | MIN, MIN => MIN
  | MAX, MAX => MAX
  | _, _ => none
