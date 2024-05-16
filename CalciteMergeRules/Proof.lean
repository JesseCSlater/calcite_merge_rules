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
    ∃ witness : Fin G → Option Nat, ∀ row ∈ table, 
      row ∈ group ↔ ∀ col : Fin G, witness col = row (group_by col)

theorem Table.common_columns_subset
  {group group' table : Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by) (is_subset : group' ⊆ group)
  : ∀ col : Fin G,
    group.get_common_columns group_by col
    = group'.get_common_columns group_by col
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
  (agg_is_stricter : grouping_is_stricter agg.group_by group_by)
  (is_group : group.is_group_of table group_by)
  : group.apply_agg agg ⊆ table.apply_agg agg
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
          apply Exists.intro (group.apply_agg fst)
          apply And.intro
          case left =>
            rw [Table.group_iff (Table.apply_agg table fst) (Table.apply_agg group fst) snd.group_by]
            apply And.intro
            case left =>
              apply Table.apply_agg_to_group (Aggregate.fst_stricter_than_merge merged_succesfully)
              exact is_group
            case right =>
              apply Exists.intro (λ g => row (Fin.castAdd A' g))
              intro row' row'_from_apply_fst_table
              apply Iff.intro
              case mp =>
                intro row'_from_apply_fst_group col
                rw [← group_forms_row, ← merged_eq]
                simp_all
                apply Exists.elim row'_from_apply_fst_group
                intro group' x
                let ⟨group'_elem_group, row'_eq⟩ := x
                clear x
                rw [← row'_eq, Fin.lt_help (groups_lt_G col), Fin.append_left]
                let group'_subset_group := (Table.group_iff group group' fst.group_by).mp group'_elem_group |> And.left
                let h := (Table.common_columns_subset is_group group'_subset_group) col
                aesop_subst [row'_eq, group_forms_row, merged_eq]
                simp_all only [h]
                unfold Table.get_common_columns
                simp only
              case mpr =>
                intro columns_align
                simp_all only [Table.apply_agg, Multiset.mem_map]

                sorry
          case right =>
            sorry
        case mpr =>
          sorry


#minimize_imports

def f (n : Nat) := 
  n + 1

def g (n : Nat) :=
  f (f n)

#help attr
example 


