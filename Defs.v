Add LoadPath "D:\DVM".
Require Export Primitives.
Require Import String.

Definition Location := nat.

Definition Name := string.

Definition Register := Location.

Definition ProgramCounter := Location.

Definition ClassLocation := Location.
Definition FieldLocation := Location.
Definition MethodLocation := Location.
Definition ObjectLocation := Location.
Definition Cursor := Location.

Definition ClassName := Name.
Definition FieldName := Name.
Definition MethodName := Name.

Inductive Constant : Type :=
  | cnat : nat -> Constant
(*  | cstr : Name -> Constant  
    for later purpose*)
  | ctrue : Constant
  | cfalse : Constant
  | cnull : Constant.

Inductive type : Type :=
  | p : PrimType -> type
  | r : RefType -> type
  | v : type
with RefType : Type :=
  | c : ClassLocation -> RefType
  | a : type -> RefType
  | sizeda : type -> nat -> RefType.

Inductive lhs : Type :=
  | reg : Register -> lhs
  | acc : Register -> Register -> lhs
  | ifield : Register -> FieldLocation -> lhs
  | sfield : FieldLocation -> lhs
with rhs : Type :=
  | l : lhs -> rhs
  | cs : Constant -> rhs.

Inductive Instruction : Type :=
  | nop : Instruction
  | ret : Instruction
  | retTo : Register -> Instruction
  | invokes : list rhs -> MethodLocation -> Instruction
  | invokei : Register -> list rhs -> MethodLocation -> Instruction
  | goto : ProgramCounter -> Instruction
  | branch : rhs -> BinaryCompOperator -> rhs -> ProgramCounter -> Instruction
  | move : Register -> rhs -> Instruction
  | update : rhs -> rhs -> Instruction
  | unary : Register -> UnaryOperator -> rhs -> Instruction
  | binaryArith : Register -> rhs -> BinaryArithOperator -> rhs -> Instruction
  | new : Register -> ClassLocation -> Instruction
  | newarr : Register -> type -> rhs -> Instruction
  | cast : Register -> type -> rhs -> Instruction
  | read : Register -> Instruction
  | print : rhs -> Instruction.

Inductive MethodSig : Type := ms (am:nat) (mn:MethodName) (ret:type) (regs:nat) (args:list (type*Name)).
Inductive MethodBody : Type := mb (insts:list (ProgramCounter*Instruction)).

Inductive Method : Type := mtd (ml:MethodLocation) (mb:MethodBody).

Inductive Field : Type := fld (am:nat) (fn:FieldName) (ft:type).

Inductive Class : Type :=
  | top : Class
  | class : nat -> ClassLocation -> list FieldLocation -> list MethodLocation -> Class.

(* Accessmodifier then superclass then fields then methods *)

Inductive Ref : Type :=
  | lRef : Location -> Ref
  | null : Ref.

Inductive Val : Type :=
  | prim : Prim -> Val
  | ref : Ref -> Val.

(** 

An Object either is instance of Top class, or it made of current Class Location (Used in Casting),
Original Class Location, Field Value Pairs, or it is deletedObject which comes into play during Garbage Collection.

*)

Inductive Object : Type :=
  | topObj : Object
  | obj : ClassLocation -> ClassLocation -> list (FieldLocation * Val) -> Object
  | dobj : Object.

Inductive Array : Type :=
  | arr : nat -> list Val -> Array.

Inductive arrOrObj : Type :=
  | ar : Array -> arrOrObj
  | dob : Object -> arrOrObj.

Inductive ValOrRef : Type :=
  | vl : Val -> ValOrRef
  | rf : arrOrObj -> ValOrRef.

Inductive Program : Type := prog (cnl:list ClassName) (mnl:list MethodSig) (cl:list Class) (fl:list Field) (ml:list Method).