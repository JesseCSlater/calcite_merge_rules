import CalciteMergeRules.Table
import Mathlib.Data.Multiset.Fintype

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

theorem Table.row_in_group_if
  {group table: Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat} 
  (is_group : group.is_group_of table group_by) :  
  ∀ row ∈ table, ∀ g : Fin G, row (group_by g) = group.get_common_columns group_by g
  := by sorry

theorem Table.common_columns_subset
  {group group' table : Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by) (is_subset : group' ⊆ group)
  : ∀ g : Fin G,
    group.get_common_columns group_by g
    = group'.get_common_columns group_by g
  := by sorry

/- Proof will be easy once classes is rewritten on lists
-/
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

def grouping_is_stricter 
  (strict : Fin H → I) (loose : Fin G → I) 
  := ∀ h : Fin H, ∃ g : Fin G, loose g = strict h

theorem Table.apply_agg_to_group
  {table group : Table I} {agg : Aggregate I G A} {group_by : Fin H → Fin I}
  (agg_is_striacter : grouping_is_stricter agg.group_by group_by)
  (is_group : group.is_group_of table group_by)
  : group.apply_agg agg ⊆ table.apply_agg agg
  := by sorry

theorem Table.apply_agg_preserves_group_by
  {table group : Table I} {agg : Aggregate I G A} 
  (group_by : Fin H → Fin I)
  (agg_is_stricter : grouping_is_stricter agg.group_by group_by)
  (is_group : group.is_group_of table agg.group_by)
  : (group.apply_agg agg) 
    (group.apply_agg agg).get_common_columns group_by g'
    = table.get_common_columns agg.group_by ((group_by g').castLT' (groups_lt_G g'))
  := by sorry

theorem Aggregate.fst_stricter_than_merge
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  {merged : Aggregate I G' A'} 
  (merge_valid : fst.merge snd = some merged) :
  grouping_is_stricter fst.group_by merged.group_by 
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

theorem Fin.lt_help 
  {i : Fin (n + m)} (h : i.val < n)
  : i = Fin.castAdd m (Fin.castLT' i h) 
  := by apply Eq.refl

theorem Aggregate.merge_valid
  (table : Table I)
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A')  :
  fst.merge snd = some merged →
    table.apply_agg merged = (table.apply_agg fst |>.apply_agg snd)
    := by
    intro merged_succesfully
    let merged_eq : merge fst snd = some merged := by exact merged_succesfully
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
        simp_all only [Multiset.mem_map]
        apply Iff.intro
        case mp =>
          intro row_comes_from_group
          apply Exists.elim row_comes_from_group
          intro group x
          let ⟨is_group, group_forms_row⟩ := x
          rw [Table.group_iff] at is_group
          clear x
          have h : (group.apply_agg fst).is_group_of (table.apply_agg fst) snd.group_by := by
            apply And.intro
            case left =>
              apply Table.apply_agg_to_group (Aggregate.fst_stricter_than_merge merged_succesfully)
              exact is_group
            case right =>
              apply Exists.intro (λ g => row (Fin.castAdd A' g))
              intro row' row'_from_apply_fst_table
              apply Iff.intro
              case mp =>
                intro row'_from_apply_fst_group g'
                rw [← group_forms_row, ← merged_eq]
                simp_all
                apply Exists.elim row'_from_apply_fst_group
                intro group' x
                let ⟨group'_elem_group, row'_eq⟩ := x
                clear x
                rw [← row'_eq, Fin.lt_help (groups_lt_G g'), Fin.append_left]
                have group'_subset_group := (Table.group_iff group group' fst.group_by).mp group'_elem_group |> And.left
                have h := (Table.common_columns_subset is_group group'_subset_group) g'
                aesop_subst [row'_eq, group_forms_row, merged_eq]
                simp_all only [h]
                unfold Table.get_common_columns
                simp only
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
                      simp_all [implies_true]
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
            apply Exists.elim (And.right h)
            intro witness witness_matches_table_apply_fst
            apply funext
            intro col
            induction col using Fin.addCases
            case h.left g' =>
              rw [Fin.append_left, ← group_forms_row, Fin.append_left]




              


              

              
              
                


          case right =>
            sorry
        case mpr =>
          sorry


