import CalciteMergeRules.Table
import Mathlib

theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

def Table.is_group_of
  (group table : Table I) (group_by : Fin G → Fin I) :=
    group ⊆ table ∧
    ∃ witness ∈ group, ∀ a ∈ table,
    a ∈ group ↔ witness ∘ group_by = a ∘ group_by

theorem Table.row_from_group
  {table : Table I} {agg : Aggregate I G A} {row : Fin (G + A) → Option Nat}
  (row_in_table_apply_agg : row ∈ table.apply_agg agg) :
  ∃ group : Table I, group.is_group_of table agg.group_by ∧
    Fin.append (group.get_common_columns agg.group_by) (group.apply_calls agg.calls) = row
  := by sorry

theorem Table.common_columns_assoc
  (group : Table I) (group_by : Fin G → Fin I)
  (f: Fin G' → Fin G)
  : group.get_common_columns (group_by ∘ f)
    = group.get_common_columns group_by ∘ f := by 
    rfl

theorem Table.agg_not_empty_not_empty
  {table : Table I} {agg : Aggregate I G A} {row' : Fin (G + A) → Option Nat}
  (row'_in_table_apply_agg : row' ∈ table.apply_agg agg) :
  ∃ row ∈ table, row' ∘ (Fin.castAdd A) = row ∘ agg.group_by :=
  by sorry

theorem Table.not_empty_agg_not_empty
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) (agg : Aggregate I G A) :
  ∃ row' ∈ (table.apply_agg agg), row' ∘ (Fin.castAdd A) = row ∘ agg.group_by :=
  by sorry

theorem Table.group_not_empty
  {table group: Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by) :
  ∃ row', row' ∈ group
  := by sorry

theorem Table.row_in_table_if_row_in_group
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_table : row ∈ group) :
  row ∈ table
  :=by sorry

theorem Table.row_in_group
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) (group_by : Fin G → Fin I)
  : ∃ group : Table I, group.is_group_of table group_by ∧ row ∈ group
  := by sorry

theorem Table.row_in_group_iff
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_table : row ∈ table) :
  row ∈ group ↔ row ∘ group_by = group.get_common_columns group_by
  := by sorry

theorem Table.row_in_group_only_if
  {group table: Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_group : row ∈ group) :
  row ∘ group_by = group.get_common_columns group_by
  := by sorry

theorem Table.rows_in_group_match
  {group table : Table I} {row row' : Fin I → Option ℕ}
  {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  (row_in_group : row ∈ group) (row'_in_group : row' ∈ group)
  : row ∘ group_by = row' ∘ group_by := by
    rw [row_in_group_only_if is_group row_in_group, row_in_group_only_if is_group row'_in_group]

@[simp]
theorem Table.group_iff
  (table group : Table I) (group_by : Fin G → Fin I)
  : group ∈ table.classes group_by ↔
      group.is_group_of table group_by
  := by sorry

theorem Table.classes_nodup
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).Nodup
  := by sorry

theorem Table.groups_eq_iff
  {table group group' : Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by) (is_group' : group'.is_group_of table group_by)
  : group = group' ↔ group.get_common_columns group_by = group'.get_common_columns group_by
  := by sorry

theorem Table.apply_agg_nodup
  (table : Table I) (agg : Aggregate I G A)
  : (table.apply_agg agg).Nodup
  := by sorry

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
  := by sorry

theorem Table.apply_agg_to_group'
  {table group: Table I} {agg : Aggregate I G A}
  (is_group : group.is_group_of table agg.group_by)
  : (group.apply_agg agg) ⊆ (table.apply_agg agg)
  := by sorry

theorem Table.group_of_group
  {table group group' : Table I}
  {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_group' : group'.is_group_of group strict)
  : group'.is_group_of table strict
  := by sorry

theorem Table.apply_agg_to_group_subset
  {agg : Aggregate I G A} {loose : Fin G' → Fin I} 
  {table group : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : group.is_group_of table loose)
  : group.apply_agg agg ⊆ table.apply_agg agg
  := by 
  refine Multiset.subset_iff.mpr ?_
  intro row' row'_in_group_apply_agg
  rcases Table.row_from_group row'_in_group_apply_agg with ⟨group', group'_is_group, rfl⟩
  simp only [Table.apply_agg, Multiset.mem_map, group_iff]
  use group'
  simp only [and_true]
  exact group_of_group restrictor is_group group'_is_group

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
    refine Multiset.subset_iff.mpr ?_
    intro row' row'_in_group'
    have row'_in_table : row' ∈ table := by 
      exact row_in_table_if_row_in_group is_group' row'_in_group'
    apply row_in_group_iff is_group row'_in_table |>.mpr
    rw [columns_match, ← restrictor.is_stricter, common_columns_assoc, ← (row_in_group_iff is_group' row'_in_table).mp row'_in_group']
    rfl
  case right => 
    rcases (group_not_empty is_group') with ⟨row', row'_in_group'⟩
    use row'
    constructor
    case left =>
      exact row'_in_group'
    case right =>
      intro row row_in_group
      constructor
      case mp =>
        intro row_in_group'
        exact rows_in_group_match is_group' row'_in_group' row_in_group'
      case mpr =>
        intro rows_match
        rw [row_in_group_only_if is_group' row'_in_group'] at rows_match
        have row_in_table : row ∈ table := by
          exact row_in_table_if_row_in_group is_group row_in_group
        apply (row_in_group_iff is_group' row_in_table).mpr
        simp_all only

def Table.group_apply_agg_group
  {agg : Aggregate I G A} {loose : Fin G' → Fin I} 
  {table group : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : group.is_group_of table loose)
  : (group.apply_agg agg).is_group_of (table.apply_agg agg) (Fin.castAdd A ∘ restrictor.restrictor)
  := by 
    constructor
    case left =>
      apply Table.apply_agg_to_group_subset restrictor is_group
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
      case mp => 
        intro row'_in_group_apply_agg
        rcases agg_not_empty_not_empty row'_in_group_apply_agg with ⟨r', r'_in_group, row'_matches_r'⟩
        rw [← Function.comp.assoc, row'_matches_r', Function.comp.assoc, restrictor.is_stricter, row_in_group_only_if is_group r'_in_group]
      case mpr =>
        intro rows_match
        rcases row_from_group row'_in_table_apply_agg with ⟨group', group'_is_group, rfl⟩
        have h : Fin.append (group'.get_common_columns agg.group_by) (group'.apply_calls agg.calls) ∘ Fin.castAdd A ∘ restrictor.restrictor = group'.get_common_columns agg.group_by ∘ restrictor.restrictor := by
          funext g'
          simp only [Function.comp_apply, Fin.append_left]
        rw [h] at rows_match
        clear h
        rw [← common_columns_assoc, restrictor.is_stricter] at rows_match
        simp only [apply_agg, Multiset.mem_map, group_iff]
        use group'
        simp only [and_true]
        exact stricter_partitions_group restrictor is_group group'_is_group rows_match


theorem Table.group_group_self
  {table group : Table I}
  {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  : group.is_group_of group group_by
  := by 
  constructor
  case left =>
    simp_all only [Multiset.Subset.refl]
  case right =>
    rcases group_not_empty is_group with ⟨row, row_in_group⟩
    use row
    refine ⟨row_in_group, ?_⟩
    intro row' row'_in_group
    simp_all only [true_iff]
    exact rows_in_group_match is_group row_in_group row'_in_group

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

def Table.common_columns_agg
  {agg : Aggregate I G A} {loose : Fin G' → Fin I} 
  {table group : Table I} (restrictor : Grouping_Restrictor agg.group_by loose)
  (is_group : group.is_group_of table loose)
  : group.get_common_columns loose =
  (group.apply_agg agg).get_common_columns (Fin.castAdd A ∘ restrictor.restrictor)
  := by 
  rcases group_not_empty is_group with ⟨row, row_in_group⟩
  rcases not_empty_agg_not_empty row_in_group agg with ⟨row', row'_in_group', row'_matches_row⟩
  rw [← row_in_group_only_if (group_apply_agg_group restrictor is_group) row'_in_group', ← Function.comp.assoc, row'_matches_row, ← row_in_group_only_if is_group row_in_group, Function.comp.assoc, restrictor.is_stricter]

def Table.group_from_group
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
    rcases row_in_group row_in_table merged.group_by with ⟨group, group_group_group_by, row_in_group⟩
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
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_eq : fst.merge snd = some merged) 
  : Fin.castAdd A ∘ (fst_stricter_than_merge merged_eq).restrictor = snd.group_by
  := by rfl

/- Proof by cases on each of the possible merges
   Should be relatively straight forward
-/
theorem AggCall.merge_valid
  (col : Multiset (Multiset (Option ℕ)))
  {fst snd merged : AggCall} (merge_valid : fst.merge snd = some merged)
  : merged.call col.join = (col.map fst.call |> snd.call)
    := by
    sorry

theorem Fin.lt_help
  {i : Fin (n + m)} (h: i < n)
  : i = Fin.castAdd m (Fin.castLT' i h)
  := by apply Eq.refl

theorem Fin.gt_help
  {i : Fin (n + m)} (h : n ≤ i)
  : i = Fin.natAdd n (Fin.castGT i h)
  := by
    unfold Fin.castGT
    simp_all only [natAdd_mk, ge_iff_le, add_tsub_cancel_of_le, Fin.eta]

theorem Aggregate.merge_valid_group
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_succesfully : fst.merge snd = some merged)
  {group table : Table I}
  (group_is_group_table_merged : group.is_group_of table merged.group_by)
  : Fin.append ((group.apply_agg fst).get_common_columns snd.group_by) ((group.apply_agg fst).apply_calls snd.calls) = Fin.append (group.get_common_columns merged.group_by) (group.apply_calls merged.calls) := by
    let restrictor := Aggregate.fst_stricter_than_merge merged_succesfully
    let ⟨restrictor_group_by, is_stricter⟩ := restrictor
    have merged_eq : Aggregate.merge fst snd = some merged := by exact merged_succesfully
    unfold Aggregate.merge at merged_eq
    split at merged_eq
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl =>
      simp_all only
      split at merged_eq
      case inr => simp_all only [imp_false]
      case inl =>
        simp_all only [Option.some.injEq]
        rename_i x all_calls_merged
        let ⟨groups_lt_G, calls_ge_G⟩ := x
        clear x
        apply funext
        intro col
        induction col using Fin.addCases
        case h.left g' =>
          rw [Fin.append_left, Fin.append_left, Table.common_columns_agg restrictor group_is_group_table_merged, Aggregate.merged_eq_snd]
        case h.right a' =>
          rw [Fin.append_right, Fin.append_right]
          let group_fst_classes := group.classes fst.group_by
          let col :=
            group_fst_classes.map
              (·.map (· (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).2))
          let col_fst_snd := col.map (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.call |> (snd.calls a').1.call
          have x : col_fst_snd = Table.apply_calls (Table.apply_agg group fst) snd.calls a' := by
            simp only [Table.apply_calls, Table.apply_agg, Multiset.map_map, Function.comp_apply]
            rw [Fin.gt_help (calls_ge_G a')]
            aesop_subst [merged_eq]
            simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff, Multiset.map_map, Function.comp_apply, Fin.append_right, Table.apply_calls, col_fst_snd, col, group_fst_classes]
          rw [← x]
          clear x
          let col_merge := (merged.calls a').1.call col.join
          have x : col_merge = Table.apply_calls group merged.calls a' := by
            simp only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Table.apply_calls, col_merge]
            have y : group.map (fun x => x (merged.calls a').2) = col.join := by
              simp only [col]
              rw [← merged_eq]
              have z := all_calls_merged a'
              split at z
              case h_2 =>
                simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, imp_false, Option.isSome_none]
              case h_1 =>
                rename_i call_o call merge_eq_some
                simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Option.isSome_some, Option.get_some]
                rw [← Multiset.map_join, Table.classes_join]
            simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map]
          rw [← x]
          clear x
          simp only [col_merge, col_fst_snd]
          have merge_valid :
            (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.merge (snd.calls a').1
            = some (merged.calls a').1 := by
              have z := all_calls_merged a'
              split at z
              case h_2 =>
                simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, imp_false, Option.isSome_none]
              case h_1 =>
                rename_i call_o call merge_eq_some
                simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Option.isSome_some, Option.get_some]
                aesop_subst [merged_eq]
                simp_all only [Option.get_some]
          rw [AggCall.merge_valid col merge_valid]

theorem Aggregate.merge_valid
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'} {merged : Aggregate I G' A'} 
  (merged_succesfully : fst.merge snd = some merged) (t : Table I)
  : t.apply_agg merged = (t.apply_agg fst).apply_agg snd
  := by
    -- Since Table.apply_agg returns a bag without duplicates, 
    -- it suffices to show that for an arbitrary row r: 
    -- r ∈ t.apply_agg merged ↔ r ∈ (t.apply_agg fst).apply_agg snd 
    rw [Multiset.Nodup.ext (by simp only [Table.apply_agg_nodup]) (by simp only [Table.apply_agg_nodup])]
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
      have g_apply_fst_group_t_snd: (g.apply_agg fst).is_group_of (t.apply_agg fst) snd.group_by := by
        rw [← Aggregate.merged_eq_snd merged_succesfully]
        simp_all only [Table.group_apply_agg_group (fst_stricter_than_merge merged_succesfully)]
      refine ⟨g_apply_fst_group_t_snd, ?_⟩
      
      -- Since merged is the result of (fst.merge snd) and 
      -- g is a group of t under merged.group_by
      -- Aggregate.merge_valid_group gives that 
      -- (g.apply_agg fst).apply_agg snd = g.apply_agg merged
      exact Aggregate.merge_valid_group merged_succesfully g_group_t_merged

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
      exact Eq.symm (merge_valid_group merged_succesfully g_is_group_t_merged)

