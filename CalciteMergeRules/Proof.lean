import CalciteMergeRules.Table
import Mathlib.Data.Multiset.Fintype

/- Proof will be easy once classes is rewritten on lists
-/
theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

/- Proof because each one must differ in group_by column
-/
theorem Table.apply_agg_nodup
  (table : Table I) (agg : Aggregate I G A)
  : (table.apply_agg agg).Nodup
  := by sorry

/- Proof by cases on each of the possible merges
   Should be relatively straight forward
-/
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
  that the conditions for a merge aremet. Those are
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
    intro merged_succesfully
    split at merged_succesfully
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl =>
      simp_all only
      split at merged_succesfully
      case inr => simp_all only [imp_false]
      case inl => 
        simp_all only [Option.some.injEq]
        rename_i h h'
        rw [Multiset.Nodup.ext]
        intro row
        unfold Table.apply_agg
        simp_all only [Multiset.mem_map]
        apply Iff.intro
        case mp =>
          intro row_comes_from_group
          apply Exists.elim row_comes_from_group
          intro table x
          let ⟨table_is_group, table_forms_row⟩ := x
          apply Exists.intro (table.apply_agg fst)
          simp_all
          apply And.intro
          case left =>
            unfold Table.classes
            intro


        case mpr =>
          sorry



        sorry

#minimize_imports
