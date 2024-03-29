import Mathlib.Data.Multiset.Fold
import Std
/- I am only representing the simplest of the Calcite aggcalls
   which are possible to merge.
-/
inductive AggCall
  | COUNT
  | SUM
  | SUM0
  | MIN
  | MAX

-- Helper instances to allow functions to be used on mutisets
instance mergeComm (op : α → α → α) [comm : Std.Commutative op]
  : Std.Commutative (Option.merge op) where
  comm := by
    intro a b
    unfold Option.merge
    cases a <;> cases b <;> simp
    apply comm.comm

instance mergeAssoc (op : α → α → α) [assoc : Std.Associative op]
  : Std.Associative (Option.merge op) where
  assoc := by
    intro a b c
    unfold Option.merge
    cases a <;> cases b <;> cases c <;> simp
    apply assoc.assoc

instance addComm : Std.Commutative (Nat.add) where
  comm := Nat.add_comm

instance addAssoc : Std.Associative (Nat.add) where
  assoc := Nat.add_assoc

/- The semantics of each of the AggCalls. Each one returns
   a single Option ℕ.
-/
def AggCall.call : AggCall → Multiset (Option ℕ) → Option ℕ
  | COUNT => some ∘ Multiset.sizeOf
  | SUM => Multiset.fold (Option.merge Nat.add) none
  | SUM0 => Multiset.fold (Option.merge Nat.add) (some 0)
  | MIN => Multiset.fold (Option.merge min) none
  | MAX => Multiset.fold (Option.merge max) (some 0)

/- The set of merges which are possible in calcite, between
   the functions I am representing.
   When writing the proof, the correctness of each of these
   merges must be shown individually. This is analogous to
   Calcite, where each of these pairs provides it's own
   override of the merge function, so each of those functions
   must be proven individually.
   (It turns out the merge implementations are all the same,
   but this would not be true for a general set of AggCalls
   and merge rules.)
-/
def AggCall.merge : AggCall → AggCall → Option AggCall
  | SUM0, COUNT => COUNT
  | SUM, SUM => SUM
  | SUM0, SUM0 => SUM0
  | MIN, MIN => MIN
  | MAX, MAX => MAX
  | _, _ => none
