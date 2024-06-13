import CalciteMergeRules.Aggregate

structure Grouping_Restrictor (strict : Fin G → Fin I) (loose : Fin G' → Fin I) where
  restrictor : Fin G' → Fin G
  is_stricter : strict ∘ restrictor = loose

theorem Table.common_columns_subgroup
  {group group' table : Table I} {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_subgroup : group'.is_group_of group strict)
    : group.get_common_columns loose
      = group'.get_common_columns strict ∘ restrictor.restrictor
  := by
  rcases group_not_empty is_subgroup with ⟨r', r'_in_group'⟩
  rw [← row_in_group_only_if is_subgroup r'_in_group', Function.comp.assoc, restrictor.is_stricter]
  have r'_in_group : r' ∈ group := by
    exact Multiset.mem_of_subset (Multiset.Le.subset is_subgroup.left) r'_in_group'
  rw[row_in_group_only_if is_group r'_in_group]

theorem Table.group_of_group
  {table group group' : Table I}
  {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_group' : group'.is_group_of group strict)
  : group'.is_group_of table strict
  := by
  constructor
  case left =>
    exact le_trans is_group'.left is_group.left
  case right =>
    rcases group_not_empty is_group' with ⟨r, r_in_group'⟩
    use r
    refine ⟨r_in_group', ?_⟩
    intro r' r'_in_table
    rw [Table.row_in_group_only_if is_group' r_in_group']
    constructor
    case h.right =>
      intro not_cols_match
      simp_all only [ne_eq, Multiset.count_eq_zero]
      by_contra r'_in_group'
      apply not_cols_match
      exact Eq.symm (common_columns_valid is_group' r'_in_group')
    case h.left =>
      intro cols_match
      have r'_in_group : r' ∈ group := by
        rw [row_in_group_iff is_group r'_in_table]
        nth_rw 1 [← restrictor.is_stricter]
        rw [← Function.comp.assoc, ← cols_match, ← common_columns_subgroup restrictor is_group is_group']
      rw [← count_row_in_group is_group r'_in_group, count_row_eq_iff is_group' r'_in_group, Table.row_in_group_iff is_group' r'_in_group, cols_match]

theorem Table.stricter_partitions_group
  {table group group' : Table I}
  {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_group' : group'.is_group_of table strict)
  (columns_match : group.get_common_columns loose = group'.get_common_columns loose)
  : group'.is_group_of group strict
  := by
  constructor
  case left =>
    rw [Multiset.le_iff_count]
    intro r
    by_cases r ∈ group
    case pos r_in_group =>
      rw [count_row_in_group is_group r_in_group]
      by_cases r ∈ group'
      case pos r_in_group' =>
        rw [count_row_in_group is_group' r_in_group']
      case neg r_not_in_group' =>
        simp_all only [not_false_eq_true, Multiset.count_eq_zero_of_not_mem, zero_le]
    case neg r_not_in_group =>
      simp_all only [not_false_eq_true, Multiset.count_eq_zero_of_not_mem, nonpos_iff_eq_zero, Multiset.count_eq_zero]
      by_contra r_in_group'
      nth_rw 2 [← restrictor.is_stricter] at columns_match
      rw [common_columns_assoc, ← row_in_group_only_if is_group' r_in_group', Function.comp.assoc, restrictor.is_stricter] at columns_match
      have r_in_table : r ∈ table := row_in_table_if_row_in_group is_group' r_in_group'
      have r_in_group : r ∈ group := (row_in_group_iff is_group r_in_table).mpr columns_match.symm
      simp_all only [not_true_eq_false]
  case right =>
    rcases (group_not_empty is_group') with ⟨row', row'_in_group'⟩
    use row'
    constructor
    case left =>
      exact row'_in_group'
    case right =>
      intro row row_in_group
      constructor
      case right =>
        intro not_cols_match
        simp_all only [ne_eq, Multiset.count_eq_zero]
        by_contra row_in_group'
        apply not_cols_match
        exact rows_in_group_match is_group' row'_in_group' row_in_group'
      case left =>
        intro cols_match
        rw [row_in_group_only_if is_group' row'_in_group'] at cols_match
        have row_in_table : row ∈ table := by
          exact row_in_table_if_row_in_group is_group row_in_group
        have row_in_group' := (row_in_group_iff is_group' row_in_table).mpr
        simp_all only [true_implies]
        rw [count_row_in_group is_group row_in_group, count_row_in_group is_group' row_in_group']

theorem Table.apply_agg_to_group_le
  {agg : Aggregate I G A} {loose : Fin G' → Fin I}
  {t g : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : g.is_group_of t loose)
  : g.apply_agg agg ≤ t.apply_agg agg
  := by
  rw [Multiset.le_iff_subset (apply_agg_nodup g agg)]
  apply Multiset.subset_iff.mpr
  intro row' row'_in_group_apply_agg
  rcases Table.row_from_group row'_in_group_apply_agg with ⟨group', group'_is_group, rfl⟩
  simp only [Table.apply_agg, Multiset.mem_map, group_iff]
  use group'
  simp only [and_true]
  exact group_of_group restrictor is_group group'_is_group

theorem Table.group_apply_agg_group
  {agg : Aggregate I G A} {loose : Fin G' → Fin I}
  {table group : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : group.is_group_of table loose)
  : (group.apply_agg agg).is_group_of (table.apply_agg agg) (Fin.castAdd A ∘ restrictor.restrictor)
  := by
    constructor
    case left =>
      apply Table.apply_agg_to_group_le restrictor is_group
    case right =>
      rcases Table.group_not_empty is_group with ⟨row, row_in_group⟩
      rcases Table.not_empty_agg_not_empty row_in_group agg with ⟨row', row'_in_group_apply_agg, row'_matches_row⟩
      use row'
      refine ⟨row'_in_group_apply_agg, ?_⟩
      rcases agg_not_empty_not_empty row'_in_group_apply_agg with ⟨r', r'_in_group, row'_matches_r'⟩
      rw [← Function.comp.assoc, row'_matches_r', Function.comp.assoc, restrictor.is_stricter, row_in_group_only_if is_group r'_in_group]
      clear r'_in_group r' row'_matches_r' row'_in_group_apply_agg row' row'_matches_row
      intro row' row'_in_table_apply_agg
      constructor
      case right =>
        intro not_cols_match
        simp_all only [apply_agg, Multiset.mem_map, group_iff, ne_eq, Multiset.count_eq_zero, not_exists, not_and]
        intro group' is_group'
        by_contra group'_forms_row
        apply not_cols_match
        funext g
        rw [← group'_forms_row, Function.comp_apply, Function.comp_apply, Fin.append_left, Table.common_columns_subgroup restrictor is_group is_group']
        rfl
      case left =>
        intro cols_match
        rcases row_from_group row'_in_table_apply_agg with ⟨group', group'_is_group, row'_eq_group'⟩
        have h : Fin.append (group'.get_common_columns agg.group_by) (group'.apply_calls agg.calls) ∘ Fin.castAdd A ∘ restrictor.restrictor = group'.get_common_columns agg.group_by ∘ restrictor.restrictor := by
          funext g'
          simp only [Function.comp_apply, Fin.append_left]
        rw [← row'_eq_group', h, ← common_columns_assoc, restrictor.is_stricter] at cols_match
        clear h
        rw [Multiset.count_eq_one_of_mem (apply_agg_nodup table agg) (row'_in_table_apply_agg)]
        apply Multiset.count_eq_one_of_mem (apply_agg_nodup group agg)
        have group'_group_group := stricter_partitions_group restrictor is_group group'_is_group cols_match
        simp_all only [apply_agg, Multiset.mem_map, group_iff]
        use group'

@[reducible]
def Aggregate.fst_stricter_than_merge
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_eq : fst.merge snd = some merged) :
  Grouping_Restrictor fst.group_by merged.group_by where
  restrictor :=
    λ g' : Fin G' => (Fin.castLT' (snd.group_by g')
    (by
    simp_all only [Aggregate.merge]
    split at merged_eq
    case inr =>
      simp_all only [not_and, not_forall, not_le]
    case inl =>
      rename_i g'_lt_G
      exact g'_lt_G.left g'
    ))
  is_stricter := by
      simp_rw [Aggregate.merge] at merged_eq
      split at merged_eq
      case inr =>
        simp_all only [not_and, not_forall, not_le]
      case inl =>
        rename_i merge_valid x
        let ⟨g'_lt_G, a'_lt_A⟩ := x
        split at merged_eq
        case inr =>
          simp_all only [implies_true, merge.match_1.eq_2, Option.isSome_none, not_true_eq_false]
        case inl =>
          simp only [Option.some.injEq] at merged_eq
          simp_rw [← merged_eq]
          rfl

theorem Table.common_columns_agg
  {agg : Aggregate I G A} {loose : Fin G' → Fin I}
  {table group : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : group.is_group_of table loose)
  : group.get_common_columns loose =
  (group.apply_agg agg).get_common_columns (Fin.castAdd A ∘ restrictor.restrictor)
  := by
  rcases group_not_empty is_group with ⟨row, row_in_group⟩
  rcases not_empty_agg_not_empty row_in_group agg with ⟨row', row'_in_group', row'_matches_row⟩
  rw [← row_in_group_only_if (group_apply_agg_group restrictor is_group) row'_in_group', ← Function.comp.assoc, row'_matches_row, ← row_in_group_only_if is_group row_in_group, Function.comp.assoc, restrictor.is_stricter]

theorem Table.group_from_group
  {fst: Aggregate I G A} {merged: Aggregate I G' A'}
  {table : Table I} {group' : Table (G + A)}
  {restrictor : Grouping_Restrictor fst.group_by merged.group_by}
  (group'_group_table_apply_fst : group'.is_group_of (table.apply_agg fst) (Fin.castAdd A ∘ restrictor.restrictor))
  : ∃ group : Table I, group.is_group_of table merged.group_by ∧ group.apply_agg fst = group'
    := by
    rcases group_not_empty group'_group_table_apply_fst with ⟨row', row'_in_group'⟩
    have row'_in_table_apply_fst : row' ∈ table.apply_agg fst := by
      exact row_in_table_if_row_in_group group'_group_table_apply_fst row'_in_group'
    rcases agg_not_empty_not_empty row'_in_table_apply_fst with ⟨row, row_in_table, row_matches_row'⟩
    rcases row_in_group_mem row_in_table merged.group_by with ⟨group, group_group_group_by, row_in_group⟩
    have group_apply_fst_group_rest : (group.apply_agg fst).is_group_of (table.apply_agg fst) (Fin.castAdd A ∘ restrictor.restrictor) := by
      exact group_apply_agg_group restrictor group_group_group_by
    rcases not_empty_agg_not_empty row_in_group fst with ⟨r', r'_in_group_apply_fst, r'_matches_row⟩
    use group
    refine ⟨group_group_group_by, ?_⟩
    obtain rfl : group' = group.apply_agg fst := by
      rw [groups_eq_iff group'_group_table_apply_fst group_apply_fst_group_rest]
      rw [← row_in_group_only_if group'_group_table_apply_fst row'_in_group']
      rw [← row_in_group_only_if group_apply_fst_group_rest r'_in_group_apply_fst]
      rw [← Function.comp.assoc, ← Function.comp.assoc, row_matches_row', r'_matches_row]
    rfl

theorem Aggregate.merged_eq_snd
  {fst: Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_eq : fst.merge snd = some merged)
  : Fin.castAdd A ∘ (fst_stricter_than_merge merged_eq).restrictor = snd.group_by
  := by rfl

theorem AggCall.merge_valid
  (col : Multiset (Multiset (Option ℕ)))
  {fst_call snd_call merged_call : AggCall}
  (merge_valid : fst_call.merge snd_call = some merged_call)
  : merged_call.call col.join = (col.map fst_call.call |> snd_call.call)
    := by
    unfold AggCall.merge at merge_valid
    cases fst_call
    <;> cases snd_call
    <;> simp_all only [Option.some_inj]
    <;> unfold AggCall.call
    <;> simp only [← merge_valid]
    case COUNT.SUM0 =>
      rw [Function.comp_apply, Multiset.card_join, Multiset.sum_eq_foldl, ← Multiset.fold_eq_foldl]
      induction col using Multiset.induction_on
      case empty => simp [Multiset.map_zero, Multiset.foldl_zero]
      case cons g col col_eq =>
        rw [Multiset.map_cons, Multiset.map_cons, Multiset.fold_cons_left, Multiset.fold_cons_left, ← col_eq]
        rfl
    all_goals {
      rw [← Multiset.fold_bind, Multiset.map_const', Multiset.bind, Multiset.map_id']
      apply congrFun
      apply congr (by rfl)
      induction (Multiset.card col)
      rfl
      rename_i n h
      rw [Multiset.replicate_succ, Multiset.fold_cons_right, ← h]
      rfl
    }

theorem Aggregate.merge_succesfull_a'_ge_G
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_succesfully : fst.merge snd = some merged) (a' : Fin A')
  : (G ≤ (snd.calls a').2)
  := by
    unfold Aggregate.merge at merged_succesfully
    split at merged_succesfully
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl h => exact h.right a'

theorem Aggregate.merge_succesfull_column
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_succesfully : fst.merge snd = some merged) (a' : Fin A')
  : (fst.calls (Fin.castGT (snd.calls a').2 (merge_succesfull_a'_ge_G merged_succesfully a'))).1.merge (snd.calls a').1 = some (merged.calls a').1 ∧ (fst.calls ((snd.calls a').2.castGT (merge_succesfull_a'_ge_G merged_succesfully a'))).2 = (merged.calls a').2
  := by
  unfold Aggregate.merge at merged_succesfully
  split at merged_succesfully
  case inr => simp_all only [not_and, not_forall, not_le]
  case inl =>
    simp_all only
    split at merged_succesfully
    case inr =>
      simp_all only [imp_false]
    case inl all_calls_merged =>
      simp_all only [Option.some.injEq]
      have call_merged := all_calls_merged a'
      split at call_merged
      case h_2 =>
        simp_all only [imp_false, Option.isSome_none, Bool.false_eq_true]
      case h_1 call? call call_eq =>
        simp_all only [← merged_succesfully, Option.isSome_some, Option.get_some, and_self]

theorem Fin.gt_help
  {i : Fin (n + m)} (h : n ≤ i)
  : i = Fin.natAdd n (Fin.castGT i h)
  := by
    unfold Fin.castGT
    simp_all only [natAdd_mk, ge_iff_le, add_tsub_cancel_of_le, Fin.eta]

theorem Aggregate.merge_succesfull_group
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_succesfully : fst.merge snd = some merged)
  {group table : Table I}
  (group_is_group_table_merged : group.is_group_of table merged.group_by)
  : Fin.append
      ((group.apply_agg fst).get_common_columns snd.group_by)
      ((group.apply_agg fst).apply_calls snd.calls) =
    Fin.append
      (group.get_common_columns merged.group_by)
      (group.apply_calls merged.calls)
    := by
    funext col
    cases col using Fin.addCases
    case h.left g' =>
      rw [Fin.append_left, Fin.append_left, Table.common_columns_agg (fst_stricter_than_merge merged_succesfully) group_is_group_table_merged]
      rfl
    case h.right a' =>
      rw [Fin.append_right, Fin.append_right]
      have a'_ge_G := merge_succesfull_a'_ge_G merged_succesfully a'
      let col := (group.classes fst.group_by).map (·.map (· (fst.calls ((snd.calls a').2.castGT a'_ge_G)).2))
      have ⟨merged_call_eq, merged_col_eq⟩ := merge_succesfull_column merged_succesfully a'
      have col_merged := AggCall.merge_valid col merged_call_eq
      rw [← Multiset.map_join, Table.classes_join, Multiset.map_map] at col_merged
      simp_all only [Table.apply_calls]
      rw [← col_merged, Multiset.map_map, Fin.gt_help a'_ge_G]
      simp_all only [Fin.append_right, Function.comp_apply, Table.apply_calls]

theorem Aggregate.merge_valid
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'} {merged : Aggregate I G' A'}
  (merged_succesfully : fst.merge snd = some merged) (t : Table I)
  : t.apply_agg merged = (t.apply_agg fst).apply_agg snd
  := by
    -- Since Table.apply_agg returns a bag without duplicates,
    -- it suffices to show that for an arbitrary row r:
    -- r ∈ t.apply_agg merged ↔ r ∈ (t.apply_agg fst).apply_agg snd
    rw [Multiset.Nodup.ext (Table.apply_agg_nodup t merged) (Table.apply_agg_nodup (t.apply_agg fst) snd)]
    intro r
    apply Iff.intro

    -- Direction 1:
    -- r ∈ t.apply_agg merged → r ∈ (t.apply_agg fst).apply_agg snd
    case mp =>
      -- Assume r ∈ t.apply_agg merged
      intro r_from_t_apply_merged

      -- Then there exists a group g of t under merged.group_by s.t.
      -- r is the only element of g.apply_agg merged.
      -- Thus, to show r ∈ (t.apply_agg fst).apply_agg snd, it suffices to show that
      -- (g.apply_agg merged) ⊆ (t.apply_agg fst).apply_agg snd
      simp only [Multiset.mem_map] at r_from_t_apply_merged
      rcases r_from_t_apply_merged with ⟨g, g_group_t_merged, rfl⟩
      simp only [Table.group_iff] at g_group_t_merged

      -- To show that (g.apply_agg merged) ⊆ (t.apply_agg fst).apply_agg snd, it suffices to show
      -- that there exists some group α of (t.apply_agg fst) under snd.group_by
      -- s.t. (g.apply_agg merged) = (α.apply_agg snd).
      simp only [Multiset.mem_map, Table.group_iff]

      -- I claim (g.apply_agg fst) is such an α.
      -- It remains to be shown that
      -- (g.apply_agg fst) is a group of (t.apply_agg fst) under snd.group_by
      -- and (g.apply_agg fst).apply_agg snd = g.apply_agg merged
      use g.apply_agg fst


      -- Since merged is the result of (fst.merge snd) and
      -- g is a group of t under merged.group_by
      -- Table.group_apply_agg_group gives that
      -- (g.apply_agg fst) is a group of (t.apply_agg fst) under snd.group_by
      have g_apply_fst_group_t_snd : (g.apply_agg fst).is_group_of (t.apply_agg fst) snd.group_by := by
        rw [← Aggregate.merged_eq_snd merged_succesfully]
        simp_all only [Table.group_apply_agg_group (fst_stricter_than_merge merged_succesfully)]
      refine ⟨g_apply_fst_group_t_snd, ?_⟩

      -- Since merged is the result of (fst.merge snd) and
      -- g is a group of t under merged.group_by
      -- Aggregate.merge_valid_group gives that
      -- (g.apply_agg fst).apply_agg snd = g.apply_agg merged
      exact Aggregate.merge_succesfull_group merged_succesfully g_group_t_merged

    --Direction 2:
    -- r ∈ (t.apply_agg fst).apply_agg snd → r ∈ t.apply_agg merged
    case mpr =>
      --assume r ∈ (t.apply_agg fst).apply_agg snd
      intro r_from_t_apply_fst_apply_snd

      -- Then there exists a group g' of (t.apply_agg fst) under snd.group_by s.t.
      -- r is the only element of (g'.apply_agg snd).
      -- Thus, to show r ∈ (t.apply_agg merged), it suffices to show that
      -- (g'.apply_agg snd) ⊆ (t.apply_agg merged)
      simp only [Multiset.mem_map, Table.group_iff] at r_from_t_apply_fst_apply_snd
      rcases r_from_t_apply_fst_apply_snd with ⟨g', g'_group_t_apply_fst_snd, rfl⟩

      -- Since merged is the result of (fst.merge snd) and
      -- g' is a group of (t.apply_agg fst) under snd.group_by
      -- Table.group_from_group gives that
      -- there exists some group g of t under merged.group_by s.t. (g.apply_agg fst) = g'
      -- Thus, to show (g'.apply_agg snd) ⊆ (t.apply_agg merged), it suffices to show
      -- (g.apply_agg fst).apply_agg snd ⊆ (t.apply_agg merged)
      rw [← merged_eq_snd merged_succesfully] at g'_group_t_apply_fst_snd
      rcases Table.group_from_group g'_group_t_apply_fst_snd with ⟨g, g_is_group_t_merged, rfl⟩

      -- To show that (g.apply_agg fst).apply_agg snd ⊆ (t.apply_agg merged), it suffices to show
      -- that there exists some group a of t under merged.group_by s.t.
      -- (g.apply_agg fst).apply_agg snd = a.apply_agg merged
      simp only [Multiset.mem_map, Table.group_iff]

      -- I claim g is such an α.
      -- I have already shown that g is a group of t under merged, so it remains to be shown that
      -- (g.apply_agg fst).apply_agg snd = g.apply_agg merged
      use g
      refine ⟨g_is_group_t_merged, ?_⟩

      -- Since merged is the result of (fst.merge snd) and
      -- g is a group of t under merged.group_by
      -- Aggregate.merge_valid_group gives that
      -- (g.apply_agg fst).apply_agg snd = g.apply_agg merged
      exact Eq.symm (merge_succesfull_group merged_succesfully g_is_group_t_merged)
