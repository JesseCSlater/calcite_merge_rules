import CalciteMergeRules.Table
import Mathlib.Data.Multiset.Fintype
import Mathlib

/- Proof will be easy once classes is rewritten on lists
-/
theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

def Table.is_group_of
  (group table : Table I) (group_by : Fin G → Fin I) :=
    group ⊆ table ∧ 
    ∃ witness : Fin G → Option Nat, ∀ a ∈ table, 
      a ∈ group ↔ ∀ g : Fin G, witness g = a (group_by g)

theorem Table.agg_not_empty_not_empty
  {table : Table I} {agg : Aggregate I G A} {row : Fin (G + A) → Option Nat}
  (row_in_table_apply_agg : row ∈ table.apply_agg agg) :
  ∃ row', row' ∈ table :=
  by sorry

theorem Table.not_empty_agg_not_empty
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) :
  ∀ agg : Aggregate I G A, ∃ row', row' ∈ table.apply_agg agg :=
  by sorry

theorem Table.not_empty_group_not_empty
  {table group: Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) (is_group : group.is_group_of table group_by) :
  ∃ row', row' ∈ group
  := by sorry

theorem Table.row_in_table_if_row_in_group
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_table : row ∈ group) :
  row ∈ table 
  := by sorry

theorem Table.row_in_group_iff
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat} 
  (is_group : group.is_group_of table group_by) (row_in_table : row ∈ table) :  
  row ∈ group ↔ ∀ g : Fin G, row (group_by g) = group.get_common_columns group_by g
  := by sorry

theorem Table.row_in_group_only_if
  {group table: Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat} 
  (is_group : group.is_group_of table group_by) (row_in_group : row ∈ group) :  
  ∀ g : Fin G, row (group_by g) = group.get_common_columns group_by g
  := by sorry

/- Proof will be easy once classes is rewritten on lists
-/
@[simp]
theorem Table.group_iff
  (table group : Table I) (group_by : Fin G → Fin I)
  : group ∈ table.classes group_by ↔
      group.is_group_of table group_by
  := by sorry

/- Proof because each one must differ in group_by column
-/
theorem Table.apply_agg_nodup
  (table : Table I) (agg : Aggregate I G A)
  : (table.apply_agg agg).Nodup 
  := by sorry

structure Grouping_Restrictor (strict : Fin H → Fin I) (loose : Fin G → Fin I) where
  restrictor : Fin G → Fin H
  is_stricter : ∀ g : Fin G, strict (restrictor g) = loose g
  
theorem Table.stricter_partitions_group
  {table group group' : Table I}
  {strict : Fin H → Fin I} {loose : Fin G → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose) 
  (is_group' : group'.is_group_of group strict)
  : group'.is_group_of table strict
  := by sorry

theorem Table.apply_agg_to_group
  {table group : Table I} {agg : Aggregate I G A} {group_by : Fin H → Fin I}
  (restrictor : Grouping_Restrictor agg.group_by group_by)
  (is_group : group.is_group_of table group_by)
  : group.apply_agg agg ⊆ table.apply_agg agg
  := by sorry

theorem Table.common_columns_subgroup
  {group group' table : Table I} {strict : Fin H → Fin I} {loose : Fin G → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose) 
  (is_subgroup : group'.is_group_of group strict)
  : ∀ g : Fin G,
    group.get_common_columns loose g
    = group'.get_common_columns (λ g' => strict (restrictor.restrictor g')) g
  := by sorry

@[reducible]
def Aggregate.fst_stricter_than_merge
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  {merged : Aggregate I G' A'} 
  (merge_valid : fst.merge snd = some merged) :
  Grouping_Restrictor fst.group_by merged.group_by
  := 
  { restrictor := 
    λ g' : Fin G' => (Fin.castLT' (snd.group_by g') (by sorry))
    is_stricter := by sorry
}

/- Proof by cases on each of the possible merges
   Should be relatively straight forward
-/
theorem AggCall.merge_valid
  (col : Multiset (Multiset (Option ℕ)))
  {fst snd merged: AggCall} (merge_valid : fst.merge snd = some merged)
  : merged.call col.join = (col.map fst.call |> snd.call)
    := by
    sorry

theorem Fin.lt_help 
  {i : Fin (n + m)} (h : i.val < n)
  : i = Fin.castAdd m (Fin.castLT' i h) 
  := by apply Eq.refl

theorem Fin.gt_help
  {i : Fin (n + m)} (h : n ≤ i.val)
  : i = Fin.natAdd n (Fin.castGT i h)
  := by
    unfold Fin.castGT
    simp_all only [natAdd_mk, ge_iff_le, add_tsub_cancel_of_le, Fin.eta]

@[simp]
theorem Multiset.map_join (f : α → β) (S : Multiset (Multiset α)) :
    Multiset.map f (Multiset.join S) = Multiset.join (Multiset.map (Multiset.map f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons ih => simp [ih]

theorem Aggregate.merge_valid
  (table : Table I)
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A')  :
  fst.merge snd = some merged →
    table.apply_agg merged = (table.apply_agg fst |>.apply_agg snd)
    := by
    intro merged_succesfully
    have merged_eq : merge fst snd = some merged := by exact merged_succesfully
    let restrictor := Aggregate.fst_stricter_than_merge merged_succesfully
    unfold merge at merged_eq
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
        rw [Multiset.Nodup.ext]
        <;> try simp_all only [Table.apply_agg_nodup]
        intro row
        apply Iff.intro
        case mp =>
          intro row_comes_from_group
          simp_all only [Table.apply_agg, Multiset.mem_map]
          apply Exists.elim row_comes_from_group
          intro group x
          let ⟨is_group, group_forms_row⟩ := x
          simp only [Table.group_iff] at is_group
          clear x

          have h : (group.apply_agg fst).is_group_of (table.apply_agg fst) snd.group_by := by
            apply And.intro
            case left =>
              apply Table.apply_agg_to_group restrictor
              simp_all only [Table.group_iff]
            case right =>
              apply Exists.intro (λ g => row (Fin.castAdd A' g))
              intro row' row'_from_apply_fst_table
              apply Iff.intro
              case mp =>
                intro row'_from_apply_fst_group g'
                rw [← group_forms_row, ← merged_eq]
                simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff] at row'_from_apply_fst_group
                apply Exists.elim row'_from_apply_fst_group
                intro group' x
                let ⟨group'_elem_group, row'_eq⟩ := x
                clear x
                rw [← row'_eq, Fin.lt_help (groups_lt_G g'), Fin.append_left]
                have group'_subset_group := group'_elem_group |> And.left
                have h := (Table.common_columns_subgroup restrictor is_group group'_elem_group) g'
                aesop_subst [row'_eq, merged_eq, group_forms_row]
                simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff, Fin.append_left]
                apply Eq.refl
              case mpr =>
                intro row'_matches_row
                simp_all only [Table.apply_agg, Multiset.mem_map]
                apply Exists.elim row'_from_apply_fst_table
                intro group' x
                let ⟨group'_from_apply_fst_table, group'_forms_row'⟩ := x
                rw [Table.group_iff] at group'_from_apply_fst_table
                clear x
                apply Exists.intro group'
                apply And.intro
                case left => 
                  rw [Table.group_iff]
                  apply And.intro
                  case left =>
                    rw [Multiset.subset_iff]
                    intro row'' row''_in_group'
                    have row''_in_table : row'' ∈ table := by
                      apply Table.row_in_table_if_row_in_group group'_from_apply_fst_table row''_in_group'
                    have x: ∀ g : Fin G, 
                      row'' (fst.group_by g) 
                      = row' (Fin.castAdd A g) := by
                      rw [← group'_forms_row']
                      simp_all only [Fin.append_left]
                      apply Table.row_in_group_only_if group'_from_apply_fst_table row''_in_group'
                    have row''_matches_row' : ∀ g' : Fin G',
                      row'' (fst.group_by ((snd.group_by g').castLT' (groups_lt_G g'))) = 
                      row' (snd.group_by g') := by
                      intro g'
                      apply x
                    clear x
                    have row''_matches_row : ∀ g' : Fin G',
                        row'' (fst.group_by ((snd.group_by g').castLT' (groups_lt_G g'))) 
                        = row (Fin.castAdd A' g') := by
                          simp_all only [implies_true]
                    conv at row''_matches_row =>
                      intro g'
                      rw [← group_forms_row, Fin.append_left, ← merged_eq]
                      simp only
                    rw [Table.row_in_group_iff is_group row''_in_table, ← merged_eq]
                    simp_all [implies_true]
                  case right =>
                    apply Exists.intro (Table.get_common_columns group' fst.group_by)
                    intro row'' row''_in_group
                    apply Iff.intro
                    case mp =>
                      intro row''_in_group' 
                      have := Table.row_in_group_only_if group'_from_apply_fst_table row''_in_group'
                      simp_all only [implies_true]
                    case mpr =>
                      intro common_columns_match
                      have row''_in_table : row'' ∈ table := by
                        apply Table.row_in_table_if_row_in_group is_group row''_in_group
                      have := Table.row_in_group_iff group'_from_apply_fst_table row''_in_table
                      simp_all only [implies_true, iff_true]
                case right =>
                  exact group'_forms_row'

          apply Exists.intro (group.apply_agg fst)
          apply And.intro
          case left =>
            rw [Table.group_iff (Table.apply_agg table fst) (Table.apply_agg group fst) snd.group_by]
            exact h
          case right => 
            have row_in_table_apply_merged : row ∈ table.apply_agg merged := by
              simp_all only [Table.apply_agg, Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
            apply Exists.elim <| Table.agg_not_empty_not_empty row_in_table_apply_merged
            intro rowx rowx_in_table
            apply Exists.elim <| Table.not_empty_group_not_empty rowx_in_table is_group
            intro row'' row''_in_group
            apply Exists.elim <| Table.not_empty_agg_not_empty row''_in_group fst
            intro row' x
            have row'_in_group_apply_fst := x
            simp only [Table.apply_agg, Multiset.mem_map] at x
            apply Exists.elim x
            intro group' y
            let ⟨group'_group_by_fst, group'_forms_row'⟩ := y
            clear x y rowx rowx_in_table row'' row''_in_group
            rw [Table.group_iff] at group'_group_by_fst
            have row'_in_table_apply_fst : row' ∈ table.apply_agg fst := by
              simp only [Table.apply_agg, Multiset.mem_map]
              apply Exists.intro group'
              apply And.intro
              case left => 
                rw [Table.group_iff]
                apply Table.stricter_partitions_group 
                  (Aggregate.fst_stricter_than_merge merged_succesfully) 
                  is_group
                  group'_group_by_fst
              case right =>
                exact group'_forms_row'
            apply funext
            intro col
            induction col using Fin.addCases
            case h.left g' =>
              rw [Fin.append_left, ← Table.row_in_group_only_if h row'_in_group_apply_fst g', ← group'_forms_row', Fin.lt_help (groups_lt_G g'), Fin.append_left, ← group_forms_row, Fin.append_left, ← merged_eq]
              simp only
              have x := Table.common_columns_subgroup restrictor is_group group'_group_by_fst g' 
              aesop_subst [merged_eq, group'_forms_row', group_forms_row]
              simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff]
              apply Eq.refl
            case h.right a' =>
              rw [Fin.append_right, ← group_forms_row, Fin.append_right]
              let group_fst_classes := group.classes fst.group_by
              let col := 
                group_fst_classes.map 
                  (·.map (· (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).2))
              let col_fst_snd := col.map (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.call |> (snd.calls a').1.call 
              have x : col_fst_snd = Table.apply_calls (Table.apply_agg group fst) snd.calls a' := by
                simp only [Table.apply_calls, Table.apply_agg, Multiset.map_map, Function.comp_apply]
                rw [Fin.gt_help (calls_ge_G a')]
                aesop_subst [merged_eq, group'_forms_row', group_forms_row]
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
                    aesop_subst [group'_forms_row', merged_eq, group_forms_row]
                    simp_all only [Option.get_some] 
              rw [AggCall.merge_valid col merge_valid] 
        case mpr =>
          sorry


