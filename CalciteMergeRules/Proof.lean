import CalciteMergeRules.Table
import Mathlib

theorem Multiset.mem_of_count_eq_count_mem
  {s t : Multiset α} {a : α} [DecidableEq α]
  (count_eq_count : s.count a = t.count a) (mem : a ∈ t)
  : a ∈ s
  := by
  rw [← Multiset.count_pos, ← count_eq_count, Multiset.count_pos] at mem
  exact mem

theorem Multiset.count_join
  (S : Multiset (Multiset α)) (a : α) [DecidableEq α]
  : S.join.count a = (S.map (·.count a)).sum
  := by 
  induction S using Multiset.induction
  case empty => rfl
  case cons m S ih => simp_all only [join_cons, count_add, map_cons, sum_cons]

theorem Multiset.filter_dedup
  (s : Multiset α) (p : α → Prop) [DecidableEq α] [DecidablePred p]
  : s.dedup.filter p = (s.filter p).dedup
  := by
  induction s using Multiset.induction
  case empty => rfl
  case cons a s ih =>
    by_cases a ∈ s <;> by_cases p a <;> simp_all

theorem Multiset.dedup_all
  {s : Multiset α} (h : ∀ a' ∈ s, a = a') (a_in_s : a ∈ s) [DecidableEq α]
  : s.dedup = {a}
  := by 
  induction s using Multiset.induction
  case empty => simp_all only [not_mem_zero, false_implies, implies_true]
  case cons a' s' ih =>
    by_cases a ∈ s'
    case pos a_in_s' => 
      have h' : ∀ a' ∈ s', a = a' := by
        intro a' a'_in_s'
        exact h a' (mem_cons_of_mem a'_in_s')
      specialize ih h' a_in_s'
      simp_all [mem_cons, forall_eq_or_imp, true_or, dedup_cons_of_mem]
    case neg a_nin_s' =>
      rw [Multiset.Nodup.ext (nodup_dedup (a' ::ₘ s')) (nodup_singleton a)]
      simp_all only [false_implies, implies_true, mem_cons, forall_eq_or_imp, true_or, not_false_eq_true, dedup_cons_of_not_mem, mem_dedup, mem_singleton, or_iff_left_iff_imp]
      intro a'' a''_in_s'
      rw [← h.left]
      exact Eq.symm (h.right a'' a''_in_s')

theorem Table.row_in_table_if_row_in_group
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_group : row ∈ group) :
  row ∈ table
  := Multiset.mem_of_le is_group.left row_in_group

theorem Table.row_in_group
  {table : Table I} {r : Fin I → Option ℕ}
  (r_in_table : r ∈ table) (group_by : Fin G → Fin I) 
  : is_group_of (table.filter (λ r' => r ∘ group_by = r' ∘ group_by)) table group_by 
  := by
  constructor
  case left =>
    simp_all only [Multiset.filter_le]
  case right =>
    use r
    constructor
    case h.left =>
      exact Multiset.mem_filter_of_mem r_in_table rfl
    case h.right =>
      intro r' _
      constructor
      case left =>
        intro cols_match
        exact Multiset.count_filter_of_pos cols_match
      case right =>
        intro not_cols_match
        exact Multiset.count_filter_of_neg not_cols_match

theorem Table.row_in_group_eq
  {group table : Table I} {group_by : Fin G → Fin I} {r : Fin I → Option ℕ}
  (is_group : group.is_group_of table group_by) (r_in_group : r ∈ group)
  : group = table.filter (λ r' => r ∘ group_by = r' ∘ group_by)
  := by
  rcases is_group.right with ⟨w, _, is_witness⟩
  have is_witness_r := is_witness r (row_in_table_if_row_in_group is_group r_in_group)
  ext r'
  by_cases r' ∈ table
  case neg r'_nin_table =>
    simp_all only [ne_eq, Multiset.count_eq_zero, not_true_eq_false, imp_false, Decidable.not_not, Multiset.mem_filter, false_and, not_false_eq_true, Multiset.count_eq_zero_of_not_mem, implies_true, and_self]
    exact Multiset.not_mem_mono (Multiset.subset_of_le is_group.left) r'_nin_table
  case pos r'_in_table =>
    by_cases w ∘ group_by = r' ∘ group_by
    case pos cols_match =>
      simp_all only [ne_eq, Multiset.count_eq_zero, not_true_eq_false, imp_false, Decidable.not_not, Multiset.count_filter_of_pos]
    case neg not_cols_match =>
      simp_all only [ne_eq, Multiset.count_eq_zero, not_true_eq_false, imp_false, Decidable.not_not, not_false_eq_true, Multiset.count_eq_zero_of_not_mem, Multiset.mem_filter, and_false]

theorem Table.count_row_in_group
  {table group : Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  {r : Fin I → Option ℕ} (r_in_group : r ∈ group)
  : group.count r = table.count r
  := by
  rw [row_in_group_eq is_group r_in_group]
  simp only [Multiset.count_filter_of_pos]

theorem Table.common_columns_valid
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_group : row ∈ group)
  : row ∘ group_by = group.get_common_columns group_by
  := by
  unfold get_common_columns
  funext g
  have n_empty : ∃ r, r ∈ Multiset.map (fun row => row (group_by g)) group := by
    simp only [Multiset.mem_map]
    rcases is_group.right with ⟨row, row_in_group, _⟩ 
    use row (group_by g)
    use row
  rcases n_empty with ⟨r, r_in_map⟩
  have sort_ne_nil : (Multiset.sort Option.Le (Multiset.map (fun row => row (group_by g)) group)) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [Multiset.length_sort, Multiset.card_pos_iff_exists_mem]
    use r
  rcases List.exists_cons_of_ne_nil sort_ne_nil with ⟨r', l', eq_cons⟩ 
  rw [eq_cons]
  simp only [Function.comp_apply, Option.join, List.head?_cons, Option.some_bind, id_eq]
  have r'_in_sort : r' ∈ Multiset.sort Option.Le (Multiset.map (fun row => row (group_by g)) group) := by
    simp_all only [Multiset.mem_map, ne_eq, not_false_eq_true, List.mem_cons, true_or]
  simp only [Multiset.mem_sort, Multiset.mem_map] at r'_in_sort
  rcases r'_in_sort with ⟨row', row'_in_group, rfl⟩
  rcases is_group.right with ⟨witness, _, is_witness⟩
  have w_row' := is_witness row' (row_in_table_if_row_in_group is_group row'_in_group)
  have w_row := is_witness row (row_in_table_if_row_in_group is_group row_in_group)
  simp_all only [Multiset.mem_map, ne_eq, not_false_eq_true, Multiset.count_eq_zero, not_true_eq_false,
  imp_false, Decidable.not_not, implies_true, and_self, imp_self]
  have cols_eq := congr_fun w_row.right g
  simp_all only [Function.comp_apply]

theorem Table.row_in_group_iff
  {group table : Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_table : row ∈ table) :
  row ∈ group ↔ row ∘ group_by = group.get_common_columns group_by
  := by 
  constructor
  case mp =>
    intro row_in_group
    exact common_columns_valid is_group row_in_group
  case mpr =>
    intro columns_match
    rcases is_group.right with ⟨witness, witness_in_group, is_witness⟩
    specialize is_witness row row_in_table
    rw [columns_match, common_columns_valid is_group witness_in_group] at is_witness
    simp_all only [true_implies, ne_eq, not_true_eq_false, Multiset.count_eq_zero, false_implies, and_true]
    exact Multiset.mem_of_count_eq_count_mem is_witness row_in_table

theorem Table.classes_nodup
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).Nodup
  := by
  unfold classes
  simp only [Multiset.nodup_dedup]

theorem Table.row_in_group_mem
  {table : Table I} {row : Fin I → Option Nat}
  (row_in_table : row ∈ table) (group_by : Fin G → Fin I)
  : ∃ group : Table I, group.is_group_of table group_by ∧ row ∈ group
  := by 
  have h := row_in_group row_in_table group_by
  use (Multiset.filter (fun r' => row ∘ group_by = r' ∘ group_by) table)
  simp_all only [Multiset.mem_filter, and_self]

theorem Table.group_not_empty
  {table group: Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by) :
  ∃ row', row' ∈ group
  := by
  rcases is_group.right with ⟨r, r_in_group, _⟩
  use r

theorem Table.common_columns_assoc
  (group : Table I) (group_by : Fin G → Fin I)
  (f: Fin G' → Fin G)
  : group.get_common_columns (group_by ∘ f)
    = group.get_common_columns group_by ∘ f
  := by rfl

theorem Table.row_in_group_only_if
  {group table: Table I} {group_by : Fin G → Fin I} {row : Fin I → Option Nat}
  (is_group : group.is_group_of table group_by) (row_in_group : row ∈ group) :
  row ∘ group_by = group.get_common_columns group_by
  := by
  have row_in_table := row_in_table_if_row_in_group is_group row_in_group
  exact (row_in_group_iff is_group row_in_table).mp row_in_group

theorem Table.rows_in_group_match
  {group table : Table I} {row row' : Fin I → Option ℕ}
  {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  (row_in_group : row ∈ group) (row'_in_group : row' ∈ group)
  : row ∘ group_by = row' ∘ group_by := by
    rw [row_in_group_only_if is_group row_in_group, row_in_group_only_if is_group row'_in_group]

theorem Table.count_row_eq_iff
  {table group : Table I} {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  {r : Fin I → Option ℕ} (r_in_table : r ∈ table)
  : group.count r = table.count r ↔ r ∈ group
  := by
  constructor
  case mp =>
    intro count_eq
    exact Multiset.mem_of_count_eq_count_mem count_eq r_in_table
  case mpr =>
    intro r_in_group
    exact Table.count_row_in_group is_group r_in_group

theorem Table.common_columns_nodup
  (table : Table I) (group_by : Fin G → Fin I)
  : Multiset.Nodup <| (table.classes group_by).map (·.get_common_columns group_by)
  := by
  refine Multiset.Nodup.map_on ?_ (table.classes_nodup group_by)
  intro g is_group g' is_group' cols_match
  simp_all only [group_iff]
  ext r
  by_cases r ∈ table
  case neg r_not_in_table =>
    have r_not_in_g := Multiset.not_mem_mono (Multiset.Le.subset is_group.left) r_not_in_table
    have r_not_in_g' := Multiset.not_mem_mono (Multiset.Le.subset is_group'.left) r_not_in_table
    simp_all only [not_false_eq_true, Multiset.count_eq_zero_of_not_mem]
  case pos r_in_table =>
    have r_in_g_iff_g' : r ∈ g ↔ r ∈ g' := by
      rw [row_in_group_iff is_group r_in_table, cols_match, ← row_in_group_iff is_group' r_in_table]
    by_cases r ∈ g
    case neg r_not_in_g =>
      rw [Multiset.count_eq_zero_of_not_mem r_not_in_g]
      apply Eq.symm
      rw [Multiset.count_eq_zero, ← r_in_g_iff_g']
      exact r_not_in_g
    case pos r_in_g =>
      rw [count_row_in_group is_group r_in_g]
      apply Eq.symm
      rw [r_in_g_iff_g'] at r_in_g
      rw [count_row_in_group is_group' r_in_g]

 theorem Table.group_group_self
  {table group : Table I}
  {group_by : Fin G → Fin I}
  (is_group : group.is_group_of table group_by)
  : group.is_group_of group group_by
  := by
  constructor
  case left =>
    simp_all only [le_refl]
  case right =>
    rcases group_not_empty is_group with ⟨row, row_in_group⟩
    use row
    refine ⟨row_in_group, ?_⟩
    intro row' row'_in_group
    simp_all only [implies_true, ne_eq, Multiset.count_eq_zero, not_true_eq_false, imp_false, Decidable.not_not, true_and]
    exact rows_in_group_match is_group row_in_group row'_in_group

theorem Table.groups_eq_iff
  {table g g' : Table I} {group_by : Fin G → Fin I}
  (is_group : g.is_group_of table group_by) (is_group' : g'.is_group_of table group_by)
  : g = g' ↔ g.get_common_columns group_by = g'.get_common_columns group_by
  := by
  constructor
  case mp =>
    simp_all only [implies_true]
  case mpr =>
    intro cols_eq
    rw [← group_iff] at is_group is_group'
    exact Multiset.inj_on_of_nodup_map (table.common_columns_nodup group_by) g is_group g' is_group' cols_eq

theorem Table.apply_agg_nodup
  (table : Table I) (agg : Aggregate I G A)
  : (table.apply_agg agg).Nodup
  := by
  unfold Table.apply_agg
  refine Multiset.Nodup.map_on ?_ (table.classes_nodup agg.group_by)
  intro g₁ g₁_group_table  g₂ g₂_group_table cols_match
  simp_all only [Table.group_iff]
  rw [Table.groups_eq_iff g₁_group_table g₂_group_table]
  funext g'
  apply congrFun at cols_match
  specialize cols_match (Fin.castAdd A g')
  simp_all only [Fin.append_left]

theorem Table.not_empty_agg_not_empty
  {table : Table I} {r : Fin I → Option Nat}
  (r_in_table : r ∈ table) (agg : Aggregate I G A) :
  ∃ r' ∈ (table.apply_agg agg), r' ∘ (Fin.castAdd A) = r ∘ agg.group_by
  := by
  simp only [apply_agg, group_iff]
  rcases row_in_group_mem r_in_table agg.group_by with ⟨group, is_group, r_in_group⟩
  use Fin.append (group.get_common_columns agg.group_by) (group.apply_calls agg.calls)
  simp only [Multiset.mem_map, group_iff]
  constructor
  case left =>
    use group
  case right =>
    funext g
    rw [Function.comp_apply, Fin.append_left]
    apply congrFun (g := r ∘ agg.group_by)
    apply Eq.symm
    exact row_in_group_only_if is_group r_in_group

theorem Table.agg_not_empty_not_empty
  {table : Table I} {agg : Aggregate I G A} {row' : Fin (G + A) → Option Nat}
  (row'_in_table_apply_agg : row' ∈ table.apply_agg agg) :
  ∃ row ∈ table, row' ∘ (Fin.castAdd A) = row ∘ agg.group_by
  := by
  simp only [apply_agg, Multiset.mem_map, group_iff] at row'_in_table_apply_agg
  rcases row'_in_table_apply_agg with ⟨group, is_group, rfl⟩
  rcases group_not_empty is_group with ⟨row, row_in_group⟩
  use row
  refine ⟨row_in_table_if_row_in_group is_group row_in_group, ?_⟩
  funext g
  rw [Function.comp_apply, Fin.append_left]
  apply congrFun (g := row ∘ agg.group_by)
  apply Eq.symm
  exact row_in_group_only_if is_group row_in_group

theorem Table.row_from_group
  {table : Table I} {agg : Aggregate I G A} {row : Fin (G + A) → Option Nat}
  (row_in_table_apply_agg : row ∈ table.apply_agg agg) :
  ∃ group : Table I, group.is_group_of table agg.group_by ∧
    Fin.append (group.get_common_columns agg.group_by) (group.apply_calls agg.calls) = row
  := by
  simp_all only [apply_agg, Multiset.mem_map, group_iff]

theorem Table.classes_join
  (table : Table I) (group_by : Fin G → Fin I)
  : (table.classes group_by).join = table
  := by
  ext r
  by_cases r ∈ table
  case neg r_nin_table =>
    simp_all only [not_false_eq_true, Multiset.count_eq_zero_of_not_mem, Multiset.count_eq_zero, Multiset.mem_join, group_iff, not_exists, not_and]
    intro group is_group
    exact Multiset.not_mem_mono (Multiset.subset_of_le is_group.left) r_nin_table
  case pos r_in_table =>
    rw [← Multiset.filter_add_not (λ g => r ∈ g) (table.classes group_by), Multiset.join_add, Multiset.count_add]
    simp only [Multiset.mem_join, Multiset.mem_filter, group_iff, not_exists, not_and, and_imp, imp_self, implies_true, Multiset.count_eq_zero_of_not_mem, add_zero]
    unfold classes
    rw [Multiset.count_join, Multiset.filter_dedup, Multiset.filter_filter]
    let g := table.filter (λ r' => r ∘ group_by = r' ∘ group_by)
    have is_group := row_in_group r_in_table group_by
    have r_in_g : r ∈ g := Multiset.mem_filter_of_mem r_in_table rfl
    have h : ∀ g' ∈ Multiset.filter (fun a => r ∈ a ∧ is_group_of a table group_by) (Multiset.powerset table), g = g' := by
      intro g'
      simp_all only [Multiset.mem_filter, Multiset.mem_powerset, and_imp]
      intro _ r_in_g' is_group'
      rw [groups_eq_iff is_group is_group']
      rw [← row_in_group_only_if is_group r_in_g, ← row_in_group_only_if is_group' r_in_g']
    have h' : (Multiset.filter (fun a => r ∈ a ∧ is_group_of a table group_by) (Multiset.powerset table)).dedup = {g} := by
      refine Multiset.dedup_all h ?_
      simp_all only [Multiset.mem_filter, Multiset.mem_powerset, and_imp, Multiset.filter_le, and_self, g]
    rw [h']
    simp only [g]
    simp_all only [Multiset.mem_filter, Multiset.mem_powerset, and_imp, le_refl, Multiset.map_singleton, Multiset.count_filter_of_pos, Multiset.sum_singleton]

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
  rw [row_in_group_only_if is_group r'_in_group]

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

def Table.group_apply_agg_group
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

def Aggregate.merge_succesfull_column
  {fst : Aggregate I G A} {snd : Aggregate (G + A) G' A'}
  (merged_succesfully : fst.merge snd = some merged) (a' : Fin A')
  : Σ' (h :G ≤ (snd.calls a').2),
    ∃ merged_call : AggCall,
      (fst.calls (Fin.castGT (snd.calls a').2 h)).1.merge (snd.calls a').1 = some merged_call
  where
  fst := by
    unfold Aggregate.merge at merged_succesfully
    split at merged_succesfully
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl h => exact h.right a'
  snd := by
    unfold Aggregate.merge at merged_succesfully
    split at merged_succesfully
    case inr => simp_all only [not_and, not_forall, not_le]
    case inl h =>
      simp_all only
      split at merged_succesfully
      case inr => simp_all only [imp_false]
      case inl all_calls_merged =>
        simp_all only [Option.some.injEq]
        have call_merged := all_calls_merged a'
        split at call_merged
        case h_2 => simp_all only [imp_false, Option.isSome_none, Bool.false_eq_true]
        case h_1 call? call call_eq =>
          use call

theorem Aggregate.merge_valid_group
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
    apply funext
    intro col
    induction col using Fin.addCases
    case h.left g' =>
      rw [Fin.append_left, Fin.append_left]
      rw [Table.common_columns_agg (fst_stricter_than_merge merged_succesfully) group_is_group_table_merged]
      rfl
    case h.right a' =>
      rw [Fin.append_right, Fin.append_right]
      unfold Aggregate.merge at merged_succesfully
      split at merged_succesfully
      case inr => simp_all only [not_and, not_forall, not_le]
      case inl h =>
        simp_all only
        split at merged_succesfully
        case inr => simp_all only [imp_false]
        case inl all_calls_merged =>
          simp_all only [Option.some.injEq]
          rcases h with ⟨group_lt_G, calls_ge_G⟩
          have call_merged := all_calls_merged a'
          split at call_merged
          case h_2 => simp_all only [imp_false, Option.isSome_none, Bool.false_eq_true]
          case h_1 call? call' merge_eq_some' =>
            let group_fst_classes := group.classes fst.group_by
            let col :=
              group_fst_classes.map
                (·.map (· (fst.calls ((snd.calls a').2.castGT (calls_ge_G a'))).2))
            let col_fst_snd := col.map (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.call |> (snd.calls a').1.call
            have x : col_fst_snd = Table.apply_calls (Table.apply_agg group fst) snd.calls a' := by
              simp only [Table.apply_calls, Table.apply_agg, Multiset.map_map, Function.comp_apply]
              rw [Fin.gt_help (calls_ge_G a')]
              aesop_subst [merged_succesfully]
              simp_all only [Table.apply_agg, Multiset.mem_map, Table.group_iff, Multiset.map_map, Function.comp_apply, Fin.append_right, Table.apply_calls, col_fst_snd, col, group_fst_classes]
            rw [← x]
            clear x
            let col_merge := (merged.calls a').1.call col.join
            have x : col_merge = Table.apply_calls group merged.calls a' := by
              simp only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Table.apply_calls, col_merge]
              have y : group.map (fun x => x (merged.calls a').2) = col.join := by
                simp only [col]
                rw [← merged_succesfully]
                simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Option.isSome_some, Option.get_some]
                rw [← Multiset.map_join, Table.classes_join]
              simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map]
            rw [← x]
            clear x
            simp only [col_merge, col_fst_snd]
            have merge_valid :
              (fst.calls (Fin.castGT (snd.calls a').2 (calls_ge_G a'))).1.merge (snd.calls a').1
              = some (merged.calls a').1 := by
                  simp_all only [Table.group_iff, Table.apply_agg, Multiset.mem_map, Option.isSome_some, Option.get_some]
                  aesop_subst [merged_succesfully]
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



