Add LoadPath "D:\DVM".
Require Export Helpers.

Module Type ListType.
  Parameter t1 : Type.
  Definition t2 := list t1.
  Definition empty : t2 := nil.
  Definition app (x:t1) (l:t2) := (cons x l).
  Fixpoint remove (x:t1) (comp:t1 -> t1 -> bool) (l:t2) :=
    match l with
    | nil => nil
    | (cons x' ls) => match (comp x x') with
      | true => (remove x comp ls)
      | false => (cons x' (remove x comp ls))
      end
    end.
  Fixpoint find (x:t1) (comp:t1 -> t1 -> bool) (l:t2) : (@Option nat) :=
    match l with
    | nil => None
    | (cons x' ls) => match (comp x x') with
      | true => (Some 0)
      | false => match (find x comp ls) with
        | None => None
        | Some n => Some (n+1)
        end
      end
    end.
  Fixpoint get (n:nat) (l:t2) : @Option t1 :=
    match n,l with
    | _,nil => None
    | 0,(cons hd tl) => Some hd
    | (S n),(cons hd tl) => (get (n) tl)
    end.
  Fixpoint set (n:nat) (x:t1) (l:t2) : t2 :=
    match n,l with
    | _,nil => nil
    | 0,(cons x' ls) => (cons x ls)
    | (S n),(cons x' ls) => (cons x' (set n x ls))
    end.
  Fixpoint prep (x:t1) (l:t2) : t2 :=
    match l with
    | nil => (cons x nil)
    | (cons x' ls) => (cons x' (prep x ls))
    end.
  Fixpoint len (l:t2) : nat :=
    match l with
    | nil => 0
    | (cons x' ls) => (len ls) + 1
    end.
  Fixpoint rev (l:t2) : t2 :=
    match l with
    | nil => nil
    | (cons x' ls) => prep x' (rev ls)
    end.
  Fixpoint norepeat (comp:t1 -> t1 -> bool) (l:t2) : bool :=
    match l with
    | nil => true
    | (cons x' ls) => match (find x' comp ls) with
      | None => (norepeat comp ls)
      | _ => true
      end
    end.
  Fixpoint setMany (vals:list (nat*t1)) (lst:t2) : t2 :=
    match vals with
    | nil => lst
    | (cons (n1,val1) rem) => setMany rem (set n1 val1 lst)
    end.
End ListType.