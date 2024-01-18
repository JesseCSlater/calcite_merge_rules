import CalciteMergeRules.AggCalls
import CalciteMergeRules.OptionLe
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Vector.Basic

abbrev Table (numCols : ℕ) :=
  Multiset (Fin numCols → Option ℕ)

structure Aggregate (I G A : ℕ) where
  group_by : Fin G → Fin I
  calls : Fin A → AggCall × Fin I

def Table.classes
  (m : Table I) (group_by : Fin G → Fin I)
  : Multiset (Table I):=
  let x := m.powerset
  |>.filter (λ p =>
              ∀ row₁ ∈ p,
              ∀ row₂ ∈ p,
              ∀ col : Fin G,
                row₁ (group_by col) =
                  row₂ (group_by col))
  x.filter (λ p => ∀ q ∈ x, p ≤ q → p = q)

def Table.get_groups
  (table : Table I) (group_by : Fin G → Fin I)
  : Fin G → Option ℕ :=
  λ col =>
    table.map (λ row => row (group_by col))
    |>.sort Option.Le
    |>.head?
    |>.join

def Table.apply_calls
  (table : Table I) (calls : Fin A → AggCall × Fin I)
  : Fin A → Option ℕ :=
  λ col =>
    let (call, row) := calls col
    let column := table.map (· row)
    (call.call column)

def Table.apply_agg
  (table : Table I) (agg : Aggregate I G A)
  : Table (G + A) :=
  let {calls, group_by} := agg
  let groups := table.classes group_by
  groups.map (λ t =>
    Fin.append (t.get_groups group_by) (t.apply_calls calls))

def Fin.castGT {n m : Nat} (i : Fin (n + m)) (h : i.val ≥ n)
 : Fin m := ⟨i.val - n,
  by
  apply (tsub_lt_iff_left h).mpr
  simp⟩

def Fin.castLT' {n m : Nat} (i : Fin (n + m)) (h : i.val < n)
 : Fin n := ⟨i.val, by simp_all⟩

def Aggregate.merge
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A') :
  Option (Aggregate I G' A') :=
  let ⟨fst_group, fst_calls⟩ := fst
  let ⟨snd_group, snd_calls⟩ := snd
  if _ : (∀ g' : Fin G', (snd_group g').val < G)
     ∧ (∀ a' : Fin A', (snd_calls a').2.val ≥ G)
  then
    let ret_calls? :=
      (λ k =>
        let (fst_call, i) :=
          fst_calls ((snd_calls k).2.castGT (by simp_all))
        fst_call.merge (snd_calls k).1
        |>.map (·, i))
      |> Vector.mOfFn
    ret_calls?.map
      λ v => ⟨
        λ g' => (snd_group g').castLT' (by simp_all)
                      |> fst_group,
        v.get⟩
  else none
