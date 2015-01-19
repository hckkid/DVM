Require Export Defs.
Require Export DList.
Require Export Bvector.

Open Scope type_scope.

Module Type IDvmStateType.

Parameter n:nat.

Definition securityVectorType : Type := Bvector n.

Inductive Frame : Type :=  frm (vals:list (nat*securityVectorType)) (ml:MethodLocation) (PC:ProgramCounter).

Inductive ObjectVectorType : Type :=
  | topObjVect : securityVectorType -> ObjectVectorType
  | obj : ClassLocation -> ClassLocation -> list (FieldLocation * securityVectorType) -> ObjectVectorType
  | dobjVect : securityVectorType -> ObjectVectorType.

Inductive ArrayVectorType : Type :=
  | arr : nat -> list securityVectorType -> ArrayVectorType.

Inductive arrOrObj : Type :=
  | ar : ArrayVectorType -> arrOrObj
  | dob : ObjectVectorType -> arrOrObj.

Definition Heap : Type := list arrOrObj.

Definition SHeap : Type := list (FieldLocation * securityVectorType).

Definition Buffer : Type := Cursor*(list nat).

Inductive IDVMState : Type := 
  | dst (frms:list Frame) (h:Heap) (sh:SHeap) (inb:Buffer) (outb:Buffer)
  | stuck
  | halt.

Inductive frameDiff : Type :=
  | upVals : nat -> securityVectorType -> frameDiff
  | upPC : ProgramCounter -> frameDiff.

Inductive deltaState : Type :=
  | createFrame : Frame -> deltaState
  | updateFrame : frameDiff -> deltaState
  | deleteFrame : deltaState
  | addHeap : arrOrObj -> deltaState
  | upHeap : list (nat*arrOrObj) -> deltaState
  | upSHeap : SHeap -> deltaState
  | addOutb : nat -> deltaState
  | upInb : list (nat*nat) -> deltaState
  | upOutb : list (nat*nat) -> deltaState
  | upInc : Cursor -> deltaState
  | upOutc : Cursor -> deltaState
  | mkStuck : deltaState
  | mkHalt : deltaState.

