import CalciteMergeRules.Table

theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

theorem Aggcall.merge_valid
  (tables : Multiset (Table I))
  (fst snd : AggCall) :
    fst.merge snd = some merged ->

    := by
    sorry

theorem Aggregate.merge_valid
  (t : Table I)
  (fst : Aggregate G₁ I J) (snd : Aggregate G₂ J K) :
  fst.merge snd = some merged ->
    t.apply_agg merged = (t.apply_agg fst |>.apply_agg snd)
    := by
    sorry
