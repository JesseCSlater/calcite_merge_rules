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
