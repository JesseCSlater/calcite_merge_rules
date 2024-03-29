import CalciteMergeRules.Table
import Mathlib.Data.Multiset.Fintype

@[reducible, simp]
theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

theorem Table.apply_calls_valid
  (table : Table I) (group_by : Fin G → Fin I)
  : table.classes group_by
  := by sorry

theorem AggCall.merge_valid
  (col : Multiset (Multiset (Option ℕ)))
  (fst snd merged: AggCall) :
    fst.merge snd = some merged →
      merged.call col.join = (col.map fst.call |> snd.call)
    := by
    sorry

/- This is the main theorem, and I am working to prove it first,
   leaving the smaller proofs it depends on as assumptions for now.

  Proof sketch:
  First, use the assumption that the merge was successful to get
  that the conditions for a merge are met. Those are
  1. All of the group_by columns of the second aggregate
     are group_by columns of the first aggregate's output table.
  2. All the AggCalls of the second aggregate are columns
     formed from AggCalls in the first aggregate
  3. Each AggCall of the second aggregate is mergeable with the
     cooresponding AggCall of the first Aggregate
  ...
-/
theorem Aggregate.merge_valid
  (t : Table I)
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A')  :
  fst.merge snd = some merged →
    t.apply_agg merged = (t.apply_agg fst |>.apply_agg snd)
    := by
    unfold merge
    intro merge
    split at merge
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl =>
      simp_all only
      split at merge
      case inr => simp_all only [imp_false]
      case inl =>
        simp_all only [Option.some.injEq]
        rename_i h h'
        unfold Table.apply_agg Table.get_groups Table.apply_calls
        simp_all
        aesop
        sorry

#minimize_imports
