import CalciteMergeRules.AggCalls
import CalciteMergeRules.OptionLe

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

def Aggregate.merge
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A') :
  Option (Aggregate I G A') :=
  let ⟨_, fst_calls⟩ := fst
  let ⟨group_by, snd_calls⟩ := snd
  let ret_calls? :=
    (λ k =>
      let (snd_call, j) := snd_calls k
      let (fst_call, i) := fst_calls j
      fst_call.merge snd_call
      |>.map (·, i))
    |> Vector.mOfFn
  ret_calls?.map
    λ v => ⟨Prod.snd ∘ fst_calls ∘ group_by, v.get⟩
