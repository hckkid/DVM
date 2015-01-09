Require Export Helpers.

(**

* Operator Definitions

- UnaryOperator : For unary operations
- BinaryArithOperator : For Binary Arithmetic Only
- BinaryCompOperator : For comparison of two values

*)

Inductive UnaryOperator : Type :=
  | unot : UnaryOperator.

Inductive BinaryArithOperator : Type :=
  | badd : BinaryArithOperator
  | bsub : BinaryArithOperator
  | bmult : BinaryArithOperator
  | bdiv : BinaryArithOperator
  | bmod : BinaryArithOperator
.

(**
  - | band : BinaryArithOperator
  - | bor : BinaryArithOperator
  - | bxor : BinaryArithOperator 
  For later
*)

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

(**

* Signature for Functionality module on primitives

*)

Module Type PrimitiveType.
  Parameter t : Type.   (** ADT for primitives which is Prim *)
  Parameter t_type : Type. (** ADT for primitive types *)
  Parameter cast : t_type -> t -> t.
  Parameter comp : t -> t -> nat.
  Parameter toNat : t -> nat.
  Parameter fromNat : t_type -> nat -> t.
  Parameter getType : t -> t_type.
(** 
  - Axiom castToSame : forall x ty, ty = (getType x) -> (cast ty x) = x.
  - Axiom castType : forall x ty, getType (cast ty x) = ty. 
  Not a priority, since Primitives are in separate modules, there execution can be updated anytime 
  without breaking whole system
*)
End PrimitiveType.

(**

* PType an implementation module

*)

Module PType <: PrimitiveType.
(**
  Declares parameter ADTs for Primitive and PrimitiveType
*)
  Definition t := Prim.
  Definition t_type := PrimType.

(**

** Operations

  - toNat : Prim to nat conversion
  - fromNat : nat and input type to Prim of input type
  - getType : return type of current Prim
  - comp : compares two prims
  - cast : cast given prim to prim of input type

*)

  Fixpoint toNat (x:t) : nat :=
    match x with
    | boolean n => n
    | char n => n
    | int n => n
    end.

  Inductive toNatRel : t -> nat -> Prop :=
    | boolToNatRel : forall n:nat, toNatRel (boolean n) n
    | charToNatRel : forall n:nat, toNatRel (char n) n
    | intToNatRel : forall n:nat, toNatRel (int n) n.

  Theorem toNatRelEq : forall (x:t) (n:nat), toNat x = n <-> toNatRel x n.
  Proof.
    destruct x; split; intro; simpl in H; subst; try econstructor; try (inversion H; simpl; reflexivity).
  Qed.

  Fixpoint fromNat (ty:t_type) (n:nat) : t :=
    match ty with
    | Bool => boolean n
    | Char => char n
    | Int => int n
    end.

  Inductive fromNatRel : t_type -> nat -> t -> Prop :=
    | boolFromNatRel : forall n:nat, fromNatRel Bool n (boolean n)
    | charFromNatRel : forall n:nat, fromNatRel Char n (char n)
    | intFromNatRel : forall n:nat, fromNatRel Int n (int n).

  Theorem fromNatRelEq : forall (ty:t_type) (x:t) (n:nat), fromNat ty n = x <-> fromNatRel ty n x.
  Proof.
    destruct ty; split; intro; simpl in H; subst; try econstructor; try inversion H; simpl; reflexivity.
  Qed.

  Fixpoint getType (x:t) : t_type :=
    match x with
    | boolean x => Bool
    | char x => Char
    | int x => Int
    end.

  Inductive getTypeRel : t -> t_type -> Prop :=
    | boolGetTypeRel: forall n:nat, getTypeRel (boolean n) Bool
    | charGetTypeRel: forall n:nat, getTypeRel (char n) Char
    | intGetTypeRel: forall n:nat, getTypeRel (int n) Int.

  Theorem getTypeRelEq : forall (x:t) (ty:t_type), getType x = ty <-> getTypeRel x ty.
  Proof.
    destruct x; split; intro; simpl in H; subst; try econstructor; inversion H; simpl; reflexivity.
  Qed.

  Definition cast (ty:t_type) (x:t) : t :=
    fromNat ty (toNat x).

  Inductive castRel : t_type -> t -> t -> Prop:=
    | castRelConstructor : forall (x1 x2:t) (ty:t_type) (n:nat), toNatRel x1 n -> fromNatRel ty n x2 -> castRel ty x1 x2.

  Theorem castRelEq : forall (ty:t_type) (x1 x2:t), cast ty x1 = x2 <-> castRel ty x1 x2.
  Proof.
    intros; split; intro.
    unfold cast in H.
      remember (toNat x1) as n.
      econstructor. eapply toNatRelEq. symmetry. eapply Heqn.
      apply fromNatRelEq. assumption.
    inversion H. unfold cast. apply toNatRelEq in H0. subst. apply fromNatRelEq.
    assumption.
  Qed.

  Definition comp (x1 x2:t) : nat :=
    (toNat x1) - (toNat x2).

End PType.