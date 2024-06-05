import CalciteMergeRules.Table

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

def agg : Aggregate 3 2 2 where
  group_by : Fin 2 → Fin 3 :=
    λ | 0 => 2
      | 1 => 1

  calls : Fin 2 → AggCall × Fin 3 :=
    λ | 0 => (AggCall.SUM, 2)
      | 1 => (AggCall.MAX, 3)


/-
{
  ![none, some 0, some 1],
  ![none, some 2, some 3],
  ![some 1, some 0, some 1]
  }

-/
#eval T


/-
{
  {
    ![none, some 2, some 3]
  },
  {
    ![none, some 0, some 1],
    ![some 1, some 0, some 1]
  }
}
-/
#eval T.classes agg.group_by


/-
{
  ![some 3, some 2],
  ![some 1, some 0]
}
-/
#eval (T.classes agg.group_by).map (·.get_common_columns agg.group_by)


/-
{
  ![some 3, some 2, some 3, some 0],
  ![some 1, some 0, some 2, some 1]
}
-/
#eval T.apply_agg agg
