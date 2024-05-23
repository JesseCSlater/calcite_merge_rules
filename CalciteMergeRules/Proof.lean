import CalciteMergeRules.Table
import Mathlib.Data.Multiset.Fintype
import Mathlib


theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by sorry

def Table.is_group_of
  (group table : Table I) (group_by : Fin G → Fin I) :=
    group ⊆ table ∧
    ∃ witness ∈ group, ∀ a ∈ table,
      a ∈ group ↔ ∀ g, witness (group_by g) = a (group_by g)

theorem Table.row_from_group
  {table : Table I} {agg : Aggregate I G A} {row : Fin (G + A) → Option Nat}
  (row_in_table_apply_agg : row ∈ table.apply_agg agg) :
  ∃ group : Table I, group.is_group_of table agg.group_by ∧
    Fin.append (group.get_common_columns agg.group_by) (group.apply_calls agg.calls) = row
  := by sorry

theorem Table.agg_not_empty_not_empty
  {table : Table I} {agg : Aggregate I G A} {row : Fin (G + A) → Option Nat}
  (row_in_table_apply_agg : row ∈ table.apply_agg agg) :
  ∃ row' ∈ table, ∀ g, row (Fin.castAdd A g) = row' (agg.group_by g) :=
  by sorry

theorem Table.not_empty_agg_not_empty
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) :
  ∀ agg : Aggregate I G A, ∃ row', row' ∈ table.apply_agg agg :=
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
  := by sorry

theorem Table.row_in_group
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) (group_by : Fin G → Fin I)
  : ∃ group : Table I, group.is_group_of table group_by ∧ row ∈ group
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
  : group = group' ↔ ∀ g, group.get_common_columns group_by g = group'.get_common_columns group_by g
  := by sorry

theorem Table.apply_agg_nodup
  (table : Table I) (agg : Aggregate I G A)
  : (table.apply_agg agg).Nodup
  := by sorry

structure Grouping_Restrictor (strict : Fin G → Fin I) (loose : Fin G' → Fin I) where
  restrictor : Fin G' → Fin G
  is_stricter : ∀ g' : Fin G', strict (restrictor g') = loose g'

theorem Table.stricter_partitions_group
  {table group group' : Table I}
  {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_group' : group'.is_group_of table strict)
  (columns_match : group.get_common_columns loose = group'.get_common_columns loose)
  : group'.is_group_of group strict
  := by sorry

theorem Table.group_of_group
  {table group group' : Table I}
  {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_group' : group'.is_group_of group strict)
  : group'.is_group_of table strict
  := by sorry

theorem Table.group_group_self
  {table group : Table I}
  {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  : group.is_group_of group group_by
  := by sorry

theorem Table.apply_agg_to_group
  {table group : Table I} {agg : Aggregate I G A} {group_by : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor agg.group_by group_by)
  (is_group : group.is_group_of table group_by)
  : (group.apply_agg agg) ⊆ (table.apply_agg agg)
  := by sorry

theorem Table.apply_agg_to_group'
  {table group: Table I} {agg : Aggregate I G A}
  (is_group : group.is_group_of table agg.group_by)
  : (group.apply_agg agg) ⊆ (table.apply_agg agg)
  := by sorry

theorem Table.common_columns_subgroup
  {group group' table : Table I} {strict : Fin G → Fin I} {loose : Fin G' → Fin I}
  (restrictor : Grouping_Restrictor strict loose)
  (is_group : group.is_group_of table loose)
  (is_subgroup : group'.is_group_of group strict)
  : ∀ g' : Fin G',
    group.get_common_columns loose g'
    = group'.get_common_columns strict (restrictor.restrictor g')
  := by sorry

@[reducible]
def Aggregate.fst_stricter_than_merge
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  {merged : Aggregate I G' A'}
  (merged_eq : fst.merge snd = some merged) :
  Grouping_Restrictor fst.group_by merged.group_by
  :=
  { restrictor :=
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
          rename_i x
          simp only [Option.some.injEq] at merged_eq
          simp_rw [← merged_eq, implies_true]
}

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
    let ⟨restrictor_group_by, is_stricter⟩ := restrictor
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
          intro x
          have row_from_group_apply_merged := x
          simp only [Table.apply_agg, Multiset.mem_map] at x
          apply Exists.elim x
          clear x
          intro group x
          let ⟨group_is_group_table_merged, group_forms_row⟩ := x
          simp only [Table.group_iff] at group_is_group_table_merged
          clear x

          have group_apply_fst_group_of_table_apply_fst: (group.apply_agg fst).is_group_of (table.apply_agg fst) snd.group_by := by
            apply And.intro
            case left =>
              apply Table.apply_agg_to_group restrictor
              simp_all only [Table.group_iff]
            case right =>
              have row''_in_table := Table.agg_not_empty_not_empty row_from_group_apply_merged
              apply Exists.elim row''_in_table
              clear row''_in_table
              intro row'' x
              let ⟨row''_in_table, row''_matches_row⟩ := x
              clear x
              have row''_in_group : row'' ∈ group := by
                rw [Table.row_in_group_iff group_is_group_table_merged row''_in_table]
                intro g'
                rw [← row''_matches_row g',← group_forms_row, ← merged_eq]
                simp only [Fin.append_left]
              have x := Table.not_empty_agg_not_empty row''_in_group fst
              apply Exists.elim x
              intro row' row'_in_group_apply_fst
              clear x
              apply Exists.intro row'
              apply And.intro
              case left =>
                exact row'_in_group_apply_fst
              case right =>
                intro r r_in_table_apply_fst
                apply Iff.intro
                case mp =>
                  intro r_in_group_apply_fst g
                  simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff] at r_in_group_apply_fst row'_in_group_apply_fst
                  apply Exists.elim r_in_group_apply_fst
                  intro t_r x
                  let ⟨t_r_group_of_group_fst, t_r_forms_r⟩ := x
                  clear x
                  apply Exists.elim row'_in_group_apply_fst
                  intro t_row' x
                  let ⟨t_row'_group_of_group_fst, t_row'_forms_row'⟩ := x
                  clear x
                  rw [← t_r_forms_r, ← t_row'_forms_row', Fin.lt_help (groups_lt_G g)]
                  simp only [Fin.append_left]
                  rw [← Table.common_columns_subgroup restrictor group_is_group_table_merged t_r_group_of_group_fst, ← Table.common_columns_subgroup restrictor group_is_group_table_merged t_row'_group_of_group_fst]
                case mpr =>
                  intro columns_match
                  simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff] at r_in_table_apply_fst
                  apply Exists.elim r_in_table_apply_fst
                  intro group' x
                  let ⟨group'_group_table_fst, group'_forms_r⟩ := x
                  clear x
                  simp
                  have group'_group_fst : group'.is_group_of group fst.group_by := by
                    have col_match : group.get_common_columns merged.group_by = group'.get_common_columns merged.group_by := by
                      apply funext
                      intro g'
                      have x : group'.get_common_columns (λ g' => fst.group_by (Fin.castLT' (snd.group_by g') (groups_lt_G g'))) = (λ g' => r (snd.group_by g')) := by
                        rw [← group'_forms_r]
                        conv =>
                          rhs
                          intro g
                          rw [Fin.lt_help (groups_lt_G g)]
                          simp only [Fin.append_left]
                      rw [← Table.row_in_group_only_if group_is_group_table_merged row''_in_group g']
                      conv => rhs ; rw [← merged_eq, x]
                      simp only
                      rw [← columns_match g']
                      simp at row'_in_group_apply_fst
                      apply Exists.elim row'_in_group_apply_fst
                      intro group'' x
                      let ⟨group''_group_fst, group''_forms_row⟩ := x
                      clear x
                      rw [← group''_forms_row]
                      conv => rhs ; rw [Fin.lt_help (groups_lt_G g')]
                      simp only [Fin.append_left]
                      have h := Table.common_columns_subgroup restrictor group_is_group_table_merged group''_group_fst g'
                      simp_all
                      rw [← h, ← row''_matches_row g', ← group_forms_row, Fin.append_left]
                    exact Table.stricter_partitions_group restrictor group_is_group_table_merged group'_group_table_fst col_match
                  apply Exists.intro group'
                  exact ⟨group'_group_fst, group'_forms_r⟩

          simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff]
          apply Exists.intro (group.apply_agg fst)
          apply And.intro
          case left =>
            aesop_subst [group_forms_row, merged_eq]
            simp_all only [Table.apply_agg, Fin.append_left]
          case right =>
            apply Exists.elim <| Table.group_not_empty group_is_group_table_merged
            intro row'' row''_in_group
            apply Exists.elim <| Table.not_empty_agg_not_empty row''_in_group fst
            intro row' x
            have row'_in_group_apply_fst := x
            simp only [Table.apply_agg, Multiset.mem_map] at x
            apply Exists.elim x
            intro group' y
            let ⟨group'_group_by_fst, group'_forms_row'⟩ := y
            clear x y row'' row''_in_group
            rw [Table.group_iff] at group'_group_by_fst
            have row'_in_table_apply_fst : row' ∈ table.apply_agg fst := by
              simp only [Table.apply_agg, Multiset.mem_map]
              apply Exists.intro group'
              apply And.intro
              case left =>
                rw [Table.group_iff]
                exact Table.group_of_group restrictor group_is_group_table_merged group'_group_by_fst
              case right =>
                exact group'_forms_row'
            apply funext
            intro col
            induction col using Fin.addCases
            case h.left g' =>
              rw [Fin.append_left, ← Table.row_in_group_only_if group_apply_fst_group_of_table_apply_fst row'_in_group_apply_fst g', ← group'_forms_row', Fin.lt_help (groups_lt_G g'), Fin.append_left, ← group_forms_row, Fin.append_left, ← merged_eq]
              simp only
              have x := Table.common_columns_subgroup restrictor group_is_group_table_merged group'_group_by_fst g'
              aesop_subst [group_forms_row, merged_eq, group'_forms_row']
              simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff]
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
          intro z
          have row_from_fst_snd := z
          simp only [Multiset.mem_map, Table.group_iff] at z
          apply Exists.elim z
          intro group x
          let ⟨group_apply_fst_group_snd, group_forms_row⟩ := x
          clear x z
          apply Exists.elim (Table.agg_not_empty_not_empty row_from_fst_snd)
          intro row' y
          let ⟨z, row'_matches_row⟩ := y
          have row'_in_table_apply_fst := z
          simp only [Multiset.mem_map, Table.group_iff] at z
          apply Exists.elim z
          clear y z
          intro group' x
          let ⟨group'_group_by_fst, group'_forms_row'⟩ := x
          clear x
          apply Exists.elim (Table.agg_not_empty_not_empty row'_in_table_apply_fst)
          intro row'' y
          let ⟨row''_in_table, row''_matches_row'⟩ := y
          clear y
          apply Exists.elim (Table.row_in_group row''_in_table merged.group_by)
          intro group'' x
          let ⟨group''_group_by_merge, row''_in_group''⟩ := x
          clear x
          simp only [Multiset.mem_map, Table.group_iff]
          apply Exists.intro group''
          apply And.intro
          case left =>
            exact group''_group_by_merge
          case right =>
            apply funext
            intro col
            induction col using Fin.addCases
            case h.left g' =>
              rw [row'_matches_row g', Fin.lt_help (groups_lt_G g'), row''_matches_row' (Fin.castLT' (snd.group_by g') (groups_lt_G g'))]
              have := Table.row_in_group_only_if group''_group_by_merge row''_in_group'' g'
              aesop_subst [merged_eq, group'_forms_row', group_forms_row]
              simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff, Fin.append_left]
            case h.right a' =>

              have group''_apply_fst_eq_group : group''.apply_agg fst = group := by
                have row'_in_group'_apply_fst : row' ∈ (group'.apply_agg fst) := by
                  simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff]
                  rw [← group'_forms_row']
                  apply Exists.intro group'
                  simp_all only [and_true]
                  apply Table.group_group_self group'_group_by_fst
                have group'_group_group''_fst : group'.is_group_of group'' fst.group_by := by
                  have col_match : group''.get_common_columns merged.group_by = group'.get_common_columns merged.group_by := by
                    have x : group'.get_common_columns merged.group_by = (λ g' => row' (snd.group_by g')) := by
                      simp_rw [← merged_eq, ← group'_forms_row']
                      conv =>
                        rhs
                        intro g'
                        rw [Fin.lt_help (groups_lt_G g'), Fin.append_left]
                    apply funext
                    intro g'
                    simp_rw [x, ← Table.row_in_group_only_if group''_group_by_merge row''_in_group'' g', ← merged_eq]
                    have y := row''_matches_row' (Fin.castLT' (snd.group_by g') (groups_lt_G g'))
                    rw [← y, ← Fin.lt_help (groups_lt_G g')]
                  exact Table.stricter_partitions_group restrictor group''_group_by_merge group'_group_by_fst col_match
                have row'_in_group''_apply_fst : row' ∈ (group''.apply_agg fst) := by
                  have group'_fst_sub_group''_fst : group'.apply_agg fst ⊆ group''.apply_agg fst := by
                    apply Table.apply_agg_to_group' group'_group_group''_fst
                  apply Multiset.mem_of_subset group'_fst_sub_group''_fst row'_in_group'_apply_fst
                have group''_fst_group_table_fst : (group''.apply_agg fst).is_group_of (table.apply_agg fst) snd.group_by := by
                  apply And.intro
                  case left =>
                    apply Table.apply_agg_to_group restrictor group''_group_by_merge
                  case right =>
                    apply Exists.intro row'
                    apply And.intro
                    case left =>
                      exact row'_in_group''_apply_fst
                    case right =>
                      intro r r_in_table_apply_fst
                      apply Iff.intro
                      case mp =>
                        intro r_in_group''_apply_fst
                        intro g'
                        simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff] at r_in_group''_apply_fst
                        apply Exists.elim r_in_group''_apply_fst
                        intro t_r x
                        let ⟨t_r_group_group'', t_r_forms_r⟩ := x
                        clear x
                        rw [← t_r_forms_r, Fin.lt_help (groups_lt_G g'), Fin.append_left, row''_matches_row' (Fin.castLT' (snd.group_by g') (groups_lt_G g'))]
                        have row''_columns := Table.row_in_group_only_if group''_group_by_merge row''_in_group'' g'
                        simp_rw [← merged_eq] at row''_columns
                        rw [row''_columns]
                        have x := Table.common_columns_subgroup restrictor group''_group_by_merge t_r_group_group'' g'
                        simp_rw [← merged_eq] at x
                        exact x
                      case mpr =>
                        intro columns_match
                        have r_in_group := Table.row_from_group r_in_table_apply_fst
                        apply Exists.elim r_in_group
                        intro g_r x
                        let ⟨g_r_group_by_fst, g_r_forms_r⟩ := x
                        clear x
                        simp only [Table.apply_agg, Multiset.mem_map, Table.group_iff]
                        apply Exists.intro g_r
                        apply And.intro
                        case left =>
                          have col_match : group''.get_common_columns merged.group_by = g_r.get_common_columns merged.group_by := by
                            apply funext
                            intro g'
                            rw [← Table.row_in_group_only_if group''_group_by_merge row''_in_group'' g']
                            have x : g_r.get_common_columns merged.group_by = (λ g' => r (snd.group_by g')) := by
                              simp_rw [← merged_eq, ← g_r_forms_r]
                              conv =>
                                rhs
                                intro g''
                                rw [Fin.lt_help (groups_lt_G g''), Fin.append_left]
                            simp_rw [x, ← merged_eq, ← row''_matches_row' (Fin.castLT' (snd.group_by g') (groups_lt_G g')), ← Fin.lt_help (groups_lt_G g')]
                            exact columns_match g'
                          exact Table.stricter_partitions_group restrictor group''_group_by_merge g_r_group_by_fst col_match
                        case right =>
                          exact g_r_forms_r
                rw [Table.groups_eq_iff group''_fst_group_table_fst group_apply_fst_group_snd]
                intro g'
                rw [← Table.row_in_group_only_if group''_fst_group_table_fst row'_in_group''_apply_fst g', ← row'_matches_row g', ← group_forms_row]
                simp only [Fin.append_left]

              rw [← group_forms_row, ← group''_apply_fst_eq_group]
              simp only [Fin.append_right, Table.apply_calls, Table.apply_agg, Multiset.map_map, Function.comp_apply]
              rw [Fin.gt_help (calls_ge_G a')]
              simp only [Fin.append_right, Table.apply_calls]
              have call_merged := all_calls_merged a'
              split at call_merged
              case h_2 =>
                aesop_subst [merged_eq, group'_forms_row', group_forms_row]
                simp_all only [Table.apply_agg, imp_false, Option.isSome_none]
              case h_1 =>
                rename_i call? call merge_eq_call
                let fst_classes := group''.classes fst.group_by
                let merged_call := (merged.calls a').1.call
                let merged_col := (merged.calls a').2
                let col := (fst_classes.map (λ g => g.map (· merged_col)))
                let fst_call := (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.call
                let snd_call := (snd.calls a').1.call
                have x : group''.map (· merged_col) = col.join := by
                  rw [← Multiset.map_join, Table.classes_join group'' fst.group_by]
                have y : merged_call (col.join) = snd_call (col.map fst_call) := by
                  have := AggCall.merge_valid col merge_eq_call
                  aesop_subst [merged_eq, group'_forms_row', group_forms_row]
                  simp_all only [Option.isSome_some, Option.get_some, Multiset.map_map, Function.comp_apply, Table.apply_agg, Multiset.mem_map, Table.group_iff, Fin.append_left, merged_col, col, fst_classes, merged_call, snd_call, fst_call]
                aesop_subst [merged_eq, group'_forms_row', group_forms_row, group''_apply_fst_eq_group]
                simp_all only [Option.isSome_some, Option.get_some, Multiset.map_map, Function.comp_apply, Table.apply_agg, Multiset.mem_map, Table.group_iff, Fin.append_left, merged_col, col, fst_classes, merged_call, snd_call, fst_call]
