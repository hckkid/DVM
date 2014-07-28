Add LoadPath "D:\DVM".
Require Export Helpers.

Inductive UnaryOperator : Type :=
  | unot : UnaryOperator.

Inductive BinaryArithOperator : Type :=
  | badd : BinaryArithOperator
  | bsub : BinaryArithOperator
  | bmult : BinaryArithOperator
  | bdiv : BinaryArithOperator
  | bmod : BinaryArithOperator
  | band : BinaryArithOperator
  | bor : BinaryArithOperator
  | bxor : BinaryArithOperator.

Inductive BinaryCompOperator : Type :=
  | beq : BinaryCompOperator
  | blt : BinaryCompOperator
  | bgt : BinaryCompOperator.

Inductive PrimType : Type :=
  | Int | Char | Bool.

Inductive Prim : Type :=
  | boolean : nat -> Prim
  | char : nat -> Prim
  | int : nat -> Prim.

Module Type PrimitiveType.
  Parameter t : Type.   (* ADT for primitives which is Prim *)
  Parameter t_type : Type. (* ADT for primitive types *)
  Parameter cast : t_type -> t -> t.
  Parameter comp : t -> t -> nat.
  Parameter toNat : t -> nat.
  Parameter fromNat : t_type -> nat -> t.
  Parameter getType : t -> t_type.
  (*Axiom castToSame : forall x ty, ty = (getType x) -> (cast ty x) = x.
  Axiom castType : forall x ty, getType (cast ty x) = ty. *)
End PrimitiveType.

Module PType <: PrimitiveType.
  Definition t := Prim.
  Definition t_type := PrimType.
  Fixpoint toNat (x:t) : nat :=
    match x with
    | boolean n => n
    | char n => n
    | int n => n
    end.
  Fixpoint fromNat (ty:t_type) (n:nat) : t :=
    match ty with
    | Bool => boolean n
    | Char => char n
    | Int => int n
    end.
  Fixpoint getType (x:t) : t_type :=
    match x with
    | boolean x => Bool
    | char x => Char
    | int x => Int
    end.
  Definition cast (ty:t_type) (x:t) : t :=
    fromNat ty (toNat x).
  Definition comp (x1 x2:t) : nat :=
    (toNat x1) - (toNat x2).
End PType.