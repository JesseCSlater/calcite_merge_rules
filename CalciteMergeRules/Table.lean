import Std
import Mathlib

abbrev Row (numCols : ℕ) :=
  Fin numCols → Option ℕ

abbrev Table (numCols : ℕ) :=
  Multiset (Row numCols)

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

structure Aggregate (I O : ℕ) where
  calls : Fin O → (AggCall × Fin I)
  group_by : Finset (Fin I)

def Multiset.classes
  (m : Multiset α) (eq : α → α → Prop)
  [DecidableRel eq] [DecidableEq α] :=
  let x := m.powerset
  |>.filter (λ p => ∀ a ∈ p, ∀ b ∈ p, eq a b)
  x.filter (λ p => ∀ q ∈ x, p ≤ q → p = q)

def Table.apply_calls
  (table : Table i) (calls : Fin o → AggCall × Fin i)
  : Row o :=
  λ col =>
    let (call, row) := calls col
    let column := table.map (· row)
    (call.call column)

@[reducible, simp]
def Table.apply_agg
  (table : Table i) (agg : Aggregate i o)
  : Table o :=
  let {calls, group_by} := agg
  let groups := table.classes (∀ cell ∈ group_by, · cell = · cell)
  groups.map (Table.apply_calls · calls)

def AggCall.merge : AggCall → AggCall → Option AggCall
  | SUM0, COUNT => COUNT
  | SUM, SUM => SUM
  | SUM0, SUM0 => SUM0
  | MIN, MIN => MIN
  | MAX, MAX => MAX
  | _, _ => none

@[reducible, simp]
def Aggregate.merge
  (fst : Aggregate I J) (snd : Aggregate J K) :
  Option (Aggregate I K) :=
  let ⟨fst_calls, group_by⟩ := fst
  let ⟨snd_calls, _⟩ := snd
  let ret_calls? :=
    (λ k =>
      let (snd_call, j) := snd_calls k
      let (fst_call, i) := fst_calls j
      fst_call.merge snd_call
      |>.map (·, i))
    |> Vector.mOfFn
  ret_calls?.map
    λ v => ⟨v.get, group_by⟩

theorem Aggregate.merge_valid
  (t : Table I) (fst : Aggregate I J) (snd : Aggregate J K) :
  fst.merge snd = some merged ->
    t.apply_agg merged = (t.apply_agg fst |>.apply_agg snd)
    := by
    sorry
