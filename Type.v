Add LoadPath "D:\DVM".
Require Export Program.
Require Export DList.
Require Export DvmState.

Module Type type_type.
  Parameter t : Type.
  Parameter ob: Type.
  Parameter prg: Type.
  Parameter heap: Type.
  Parameter createObject : prg -> t -> heap -> (Location*heap).
  Parameter checkCast : prg -> t -> t -> bool.
  Parameter cast : prg -> t -> t -> heap -> @Option heap.
End type_type.

Module Type TYPE <: type_type.
  Definition t := type.
  Definition ob := Object.
  Definition prg := Program.
  Definition heap := Heap.
  Declare Module CLIST : ListType with Definition t1 := Class.
  Declare Module FLIST : ListType with Definition t1 := Field.
  Declare Module HEAP : ListType with Definition t1 := arrOrObj.
  Definition appTemp {A:Type} (x:A) (l:list A) : list A :=
    (cons x l).
  Fixpoint fieldListIndexed (n:nat) (c:Class) (clst:list Class) : @Option (list FieldLocation) :=
    match c,n with
    | top,_ => Some nil
    | (class _ sup flst _),(S n') => match (CLIST.get sup clst) with
      | Some cl' => match (fieldListIndexed n' cl' clst) with
         | Some flds => Some (fold flds appTemp flst)
         | None => None
         end
      | None => None
      end
    | _,_ => None
    end.

  Definition fieldList (c:Class) (clst:list Class) : @Option (list FieldLocation) :=
    fieldListIndexed (CLIST.len clst) c clst.

  Definition defaultSetter (fl:FieldLocation) (p:prg) : @Option Val :=
    match p with
    | (prog cnl mnl clst flst mlst) => match (FLIST.get fl flst) with
      | Some (fld am fn ft) => match ft with
        | p pt => match pt with
          | Int => Some (prim (int 0))
          | Char => Some (prim (char 0))
          | Bool => Some (prim (boolean 0))
          end
        | r rt => (Some (ref null))
        | _ => None
        end
      | None => None
      end
    end.

  Definition defaultedFields (l:list FieldLocation) (p:prg) : @Option (list (FieldLocation*Val)) :=
    match filter (map l (fun x:FieldLocation=>defaultSetter x p)) isNone with
    | nil => Some (map l (fun x:FieldLocation => match (defaultSetter x p) with
                      | Some v' => (x,v')
                      | None => (x,(ref null))
                      end))
    | _ => None
    end.

  Definition createObject (p:prg) (ty:t) (h:heap) : @Option (Location*heap) :=
    match ty with
    | r (c cl) => match (CLIST.get cl (PROGRAM.getClasses p)) with
      | Some cls => match (fieldList cls (PROGRAM.getClasses p)) with
        | Some lst => match (defaultedFields lst p) with
          | Some (lst') => Some ((HEAP.len h),(HEAP.prep (dob (obj cl lst')) h))
          | _ => None
          end
        | _ => None
        end
      | None => None
      end
    | _ => None
    end.

  Definition checkCast (p:prg) (ty1 ty2:t) : bool :=
    match ty1,ty2 with
    | (r (c cl1)) ,(r (c cl2)) => match (CLIST.get cl1 (PROGRAM.getClasses p)),(CLIST.get cl1 (PROGRAM.getClasses p)) with
      | Some cls1,Some cls2 => 