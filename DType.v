Require Export Program.
Require Export DList.
Require Export DvmState.

(**

* Overview

DType module deals with type related operations in DVM

* type_type Signature

We need following type related operations the most
- createObject : create an Object of given Class
- createArray : creates an Array of given type
- checkCast : checks for possibility of casting
- cast : casts and object into object of given type.

*)

Module Type type_type.
  Parameter t : Type.
  Parameter ob: Type.
  Parameter prg: Type.
  Parameter heap: Type.
  Parameter createObject : prg -> t -> heap -> @Option deltaState.
  Parameter createArray : t -> nat -> heap -> @Option deltaState.
  Parameter checkCast : prg -> t -> t -> bool.
  Parameter cast : prg -> t -> Location -> heap -> @Option deltaState.
End type_type.

(**

* TYPE module

*)

Module TYPE <: type_type.
(**

** Declarations & Definitions

*)
  Definition t := type.
  Definition ob := Object.
  Definition prg := Program.
  Definition heap := Heap.
  Declare Module CLIST : ListType with Definition t1 := Class.
  Declare Module FLIST : ListType with Definition t1 := Field.
  Declare Module HEAP : ListType with Definition t1 := arrOrObj.

  Definition appTemp {A:Type} (x:A) (l:list A) : list A :=
    (cons x l).

(**

** Helper Operations

*** fieldListIndexed
  creates list of field locations for given class

*)

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

(**

*** fieldList
  generates Field list from list of FieldLocation

*)

  Definition fieldList (c:Class) (clst:list Class) : @Option (list FieldLocation) :=
    fieldListIndexed (CLIST.len clst) c clst.

(**

*** defaultSetter
  generates list of default value from Fields based upon their type in corresponding order

*)

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

(**

*** defaultedFields
  generates list of FieldLocation Value pairs in corresponding order

*)

  Definition defaultedFields (l:list FieldLocation) (p:prg) : @Option (list (FieldLocation*Val)) :=
    match filter (map l (fun x:FieldLocation=>defaultSetter x p)) isNone with
    | nil => Some (map l (fun x:FieldLocation => match (defaultSetter x p) with
                      | Some v' => (x,v')
                      | None => (x,(ref null))
                      end))
    | _ => None
    end.

(**

** createObject

All helpers functions put together form createObject

*)

  Definition createObject (p:prg) (ty:t) (h:heap) : @Option deltaState :=
    match ty with
    | r (c cl) => match (CLIST.get cl (PROGRAM.getClasses p)) with
      | Some cls => match (fieldList cls (PROGRAM.getClasses p)) with
        | Some lst => match (defaultedFields lst p) with
          | Some (lst') => Some (addHeap (dob (obj cl cl lst')))
          | _ => None
          end
        | _ => None
        end
      | None => None
      end
    | _ => None
    end.

(**

** createArray

To create array we tak following steps
- fixpoint for generating N sized list of type A
- compute default
- generate N sized with default values
- create array using above

*)

  Fixpoint generateNList {A:Type} (n:nat) (val:A) : (list A) :=
    match n with
    | 0 => nil
    | S n' => (cons val (generateNList n' val))
    end.

  Definition defaultOf (ty:t) : Val :=
    match ty with
    | p pt => match pt with
      | Int => (prim (int 0))
      | Char => (prim (char 0))
      | Bool => (prim (boolean 0))
      end
    | _ => (ref null)
    end.

  Definition generateN (n:nat) (ty:t) : list Val :=
    generateNList n (defaultOf ty).

  Definition createArray (ty:t) (n:nat) (h:heap) : @Option deltaState :=
    match ty with
    | (r (a ty2)) => Some (addHeap (ar (arr n (generateN n ty2))))
    | _ => None
    end.

(**

** Cast

For casting we define following functionality
- isSubIndexed : given class locations tells if first is subclass of second or not
- isSub : given classes tells whether first is sub of second or not
- checkCast : check types for casting possibility
- cast : cast object into object of given type

*)

  Fixpoint isSubIndexed (p:prg) (c1 c2:ClassLocation) (n:nat) : bool :=
    match (areEqualNum c1 c2),n with
    | true,_ => true
    | false,0 => false
    | false,(S n') => match (CLIST.get c1 (PROGRAM.getClasses p)) with
      | Some cls1 => match cls1 with
        | (class _ c3 _ _) => (isSubIndexed p c3 c2 n')
        | _ => false
        end
      | _ => false
      end
    end.

  Definition isSub (p:prg) (c1 c2:ClassLocation) : bool :=
    isSubIndexed p c1 c2 (CLIST.len (PROGRAM.getClasses p)).

  Definition checkCast (p:prg) (ty1 ty2:t) : bool :=
    match ty1,ty2 with
    | (r (c cl1)) ,(r (c cl2)) => (isSub p cl1 cl2)
    | _,_ => false
    end.

  Definition cast (p:prg) (ty1:t) (l:Location) (h:heap) : @Option deltaState :=
    match (HEAP.get l h),ty1 with
    | Some (dob (obj cCurr cOrig data)),r (c cl) => match (isSub p cl cOrig) with
      | true => Some (upHeap (cons ((HEAP.len h),(dob (obj cl cOrig data))) nil))
      | _ => None
      end
    | _,_ => None
    end.

End TYPE.