import CalciteMergeRules.Table
import Mathlib

theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

-- theorem AggCall.merge_valid
--   (tables : Multiset (Table I))
--   (fst snd : AggCall) :
--     fst.merge snd = some merged ->

--     := by
--     sorry

theorem Aggregate.merge_valid
  (t : Table I)
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A')  :
  fst.merge snd = some merged ->
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
