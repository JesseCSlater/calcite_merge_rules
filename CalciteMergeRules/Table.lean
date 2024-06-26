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

structure Aggregate (I G A : ℕ) where
  group_by : Fin G → Fin I
  calls : Fin A → AggCall × Fin I

def Table.is_group_of
  (group table : Table I) (group_by : Fin G → Fin I) :=
    group ≤ table ∧
    ∃ witness ∈ group, ∀ a ∈ table,
      (witness ∘ group_by = a ∘ group_by → group.count a = table.count a)
      ∧ (witness ∘ group_by ≠ a ∘ group_by → group.count a = 0)

instance (table : Table I) (group_by : Fin G → Fin I) : 
  DecidablePred (λ group : Table I => group.is_group_of table group_by) := by
  intro group
  refine @And.decidable ?_ ?_ ?_ ?_
  case refine_1 => infer_instance
  case refine_2 =>
    refine @Multiset.decidableExistsMultiset ?_ ?_ ?_ ?_
    infer_instance

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
  (table : Table I) (group_by : Fin G → Fin I)
  : Multiset (Table I) :=
  table.powerset
  |>.filter (λ group : Table I => group.is_group_of table group_by)
  |>.dedup

@[simp]
theorem Table.group_iff
  (table group : Table I) (group_by : Fin G → Fin I)
  : group ∈ table.classes group_by ↔
      group.is_group_of table group_by
  := by 
  unfold classes is_group_of
  simp_all only [Multiset.mem_dedup, Multiset.mem_filter, Multiset.mem_powerset, and_self_left]

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
