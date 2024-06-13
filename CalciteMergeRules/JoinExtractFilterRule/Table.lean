import Mathlib

def Row I := 
  Fin I → Option Nat

def Table I :=
  List (Row I)

structure TableFilter (I : Nat) where
  condition : Row I → Bool

def Table.apply_filter
  (t : Table I) 
  (filter : TableFilter I)
  : (Table I) := t.filter filter.condition

structure Join (I J : Nat) where
  condition : Row (I + J) → Bool
  
def Table.apply_join
  (t1 : Table I) (t2 : Table J) 
  (join : Join I J)
  : Table (I + J) :=
  List.product t1 t2
  |>.map (λ ⟨r1, r2⟩ => Fin.append r1 r2)
  |>.filter join.condition

def Join.extract_filter
  (join : Join I J)
  : Join I J × TableFilter (I + J)
  := 
  ({condition := λ _ => true}, {condition := join.condition}) 
  
theorem Table.JoinExtractFilterRule_valid
  (t1 : Table I) (t2 : Table J) 
  {join extracted_join : Join I J}
  {extracted_filter : TableFilter (I + J)}
  (h_extracted : join.extract_filter = (extracted_join, extracted_filter))
  : Table.apply_join t1 t2 join = (Table.apply_join t1 t2 extracted_join).apply_filter extracted_filter
  := by 
  unfold apply_join apply_filter
  unfold Join.extract_filter at h_extracted
  aesop
  
  
