Fixpoint filterList {X:Type} (l1 l2:list X) (cmp:X->X->bool) : list X :=
  match l1 with
  | nil => nil
  | cons x xrem => 