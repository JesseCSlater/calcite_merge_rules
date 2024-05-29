import CalciteMergeRules.AggCalls
import CalciteMergeRules.OptionLe
import Mathlib
/-
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Fintype
-/

/- I choose a multiset representation because Calcite
   makes the order of rows in a table inaccessible from within
   an aggregate call. I suspect that this choice will end up
   making the proof easier, since I will be able to talk about
   equality between tables without worrying about the order of
   their entries.

   I represent data as Option ℕ because it makes things simpler
   than being generic over datatype, but still keeps the complexity
   required to handle most of the mergeable aggregate functions
   which Calcite supports.
-/

abbrev Row (numCols : ℕ) :=
  (Fin numCols → Option ℕ)

abbrev Table (numCols : ℕ) :=
  Multiset (Fin numCols → Option ℕ)

/- An aggregate in calcite consists of a list of columns to
   group by, and a list of columns to apply an aggregate function
   call too, along with the function to be applied. I represent
   these lists as functions from Fin n, so that I can define
   the width of tables inside the type system. Fin n → α is the
   cannonical way to represent a fixed length vector in Lean.

   An aggregate in Calcite also includes information about the
   method of rollup used in the resulting table. I am not
   representing this part becuase the aggregate merge rule
   requires that the inner aggregate does not have a rollup,
   and the outer aggregate's rollup can be simulated by just
   running the rollup multiple times with different group_by
   values.
-/

abbrev Group_By (I G : Nat) :=
  Fin G → Fin I

def Table.rel (T : Table I) (group_by : Group_By I G) :
  T → T → Prop :=
  λ r r' =>
    ∀ g : Fin G, r.1 (group_by g) = r'.1 (group_by g)

instance Table.instEquivGroupBy (group_by : Group_By I G) (T : Table I)
  : Equivalence (T.rel group_by) where
  refl := by sorry
  symm := by sorry
  trans := by sorry

instance t (T : Table I) (group_by : Group_By I G) : DecidableRel (T.rel group_by) :=
  inferInstanceAs <|
    @DecidableRel ((x : Row I) × Fin (Multiset.count x T))
    (λ r r' =>
      ∀ g : Fin G, r.1 (group_by g) = r'.1 (group_by g))

def Table.instSetoidGroupBy (T : Table I) (group_by : Group_By I G)
  : Setoid T where
  r := T.rel group_by
  iseqv := T.instEquivGroupBy group_by

instance (T : Table I) (group_by : Group_By I G) : DecidableRel (T.instSetoidGroupBy group_by).r := by
  unfold Setoid.r Table.instSetoidGroupBy
  infer_instance

instance (T : Table I) : DecidableEq T :=
  inferInstanceAs <| DecidableEq ((x : Row I) × Fin (Multiset.count x T))

def T : Table 3 :=
  Multiset.ofList [
  λ | 0 => none
    | 1 => some 0
    | 2 => some 1,
  λ | 0 => none
    | 1 => some 2
    | 2 => some 3,
  λ | 0 => some 1
    | 1 => some 0
    | 2 => some 1,
  ]

def group_by : Group_By 3 1 :=
  λ | 0 => 1

structure Aggregate (I G A : ℕ) where
  group_by : Group_By I G
  calls : Fin A → AggCall × Fin I

/-
λ g : Fin 2
 | 0 => 1
 | 1 => 1

Input table
1 3 4
4 5 7
1 3 3

Aggregate (I = 3) (G = 2) (A = 1)
group_by := [0, 1]d
calls := [(2, add)]

1 3 4
1 3 3 -> 1 3 7

4 5 7 -> 4 5 7

Output table
1 3 7
4 5 7
-/

/- Seperate a table into a multiset based on the equivalence
   classes of the group_by columns.
   Here, my choice of using a multiset instead of a list forces
   me to use the powerset which is quite inefficient. However,
   I suspect this definiton of the function will make it easier
   to prove Table.classes_join (in Proof.lean) than it would be
   with a list definiton.
   The best solution would be to write the list solution and then
   prove it is invariant under permutation so it could be raised
   to multiset, since this would maintain effeciency, but
-/
def Table.classes
  (m : Table I) (group_by : Fin G → Fin I)
  : Multiset (Table I) :=
  -- Start with the set of all subtables of m
  let x := m.powerset
  -- Remove all subtables which contain a pair of rows
  -- which have a mismatch in one of the group by columns.
  |>.filter (λ p =>
              ∀ row₁ ∈ p,
              ∀ row₂ ∈ p,
              ∀ col : Fin G,
                row₁ (group_by col) =
                  row₂ (group_by col))
  -- Remove all subtables which are a subset of another table
  x.filter (λ p => ∀ q ∈ x, p ≤ q → p = q)

#eval T.classes group_by

/- Get the unique element of each row which is used for
   grouping of the table which is already the result of
   breaking a larger table into equivalence classes,
   returning a row containing each of the equivalence
   class values.
   It would be better to do this by bringing in a
   proof that all data in the desired columns are equal,
   and then writing a function on lists and raising it to
   multisets.
-/
def Table.get_common_columns
  (group : Table I) (group_by : Fin G → Fin I)
  : Fin G → Option ℕ :=
  λ g =>
    group.map (λ row => row (group_by g))
    |>.sort Option.Le
    |>.head?
    |>.join

/- Apply the list of aggregate calls to a table, resulting
   in a row of the output of each of the calls.
-/
@[simp, reducible]
def Table.apply_calls
  (table : Table I) (calls : Fin A → AggCall × Fin I)
  : Fin A → Option ℕ :=
  λ a =>
    let call := calls a
    (call.1.call (table.map (· call.2)))

-- def Table.reduce_classes
--   (table : Table I) (group_by : Fin G → Fin I) (calls : Fin A → Fin I) :
--   ()

/- Apply an aggregate to a table, resulting in a table with
   a column for each group_by column and for each AggCall,
   and as many rows as there are equivalence classes on
   group_by
-/
@[simp, reducible]
def Table.apply_agg
  (table : Table I) (agg : Aggregate I G A)
  : Table (G + A) :=
  let groups := table.classes agg.group_by
  groups.map (λ t =>
    Fin.append (t.get_common_columns agg.group_by) (t.apply_calls agg.calls))

--Cast Fin m into Fin (n + m) in the natural way
def Fin.castGT {n m : Nat} (i : Fin (n + m)) (h : n ≤ i.val)
 : Fin m := ⟨i.val - n, by simp_all only [is_lt, tsub_lt_iff_left]⟩

--Cast Fin n into Fin (n + m) in the natural way
def Fin.castLT' {n m : Nat} (i : Fin (n + m)) (h : i.val < n)
 : Fin n := ⟨i.val, by simp_all only [h]⟩

/- The calcite aggregate merge rule. Merges two aggregates into
   a single one which produces the same result. Fails if the second
   aggregate does not have a group set which is a subset of the first's
   groups, and a set of agg_calls columns which is a subset of the
   first's.
   Also fails if any of the agg_calls are not supported, as seen in
   AggCalls.lean
-/
@[reducible]
def Aggregate.merge
  (fst : Aggregate I G A) (snd : Aggregate (G + A) G' A') :
  Option (Aggregate I G' A') :=
  if h : (∀ g' : Fin G', (snd.group_by g').val < G)
     ∧ (∀ a' : Fin A', G ≤ (snd.calls a').2.val)
  then
    let ret_calls? :=
      λ a' : Fin A' =>
        let fst_call : AggCall × Fin I :=
          fst.calls <|
          (snd.calls a').2.castGT (h.2 a')
        if let some call := fst_call.1.merge (snd.calls a').1
        then some (call, fst_call.2)
        else none
    if h' : ∀ a', Option.isSome (ret_calls? a')
    then
      some ⟨λ g' => (snd.group_by g').castLT' (h.1 g')
                  |> fst.group_by,
            λ a' => (ret_calls? a').get (h' a')
            ⟩
    else none
  else none
