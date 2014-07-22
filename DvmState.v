Add LoadPath "D:\DVM".
Require Export Defs.
Require Export DList.

Open Scope type_scope.

Inductive Frame : Type :=  frm (vals:list (nat*Val)) (ml:MethodLocation) (PC:ProgramCounter).

Definition Heap : Type := list arrOrObj.

Definition SHeap : Type := list (FieldLocation * Val).

Definition Buffer : Type := Cursor*(list nat).

Inductive DVMState : Type := 
  | dst (frms:list Frame) (h:Heap) (sh:SHeap) (inb:Buffer) (outb:Buffer)
  | stuck
  | halt.

Inductive frameDiff : Type :=
  | upVals : nat -> Val -> frameDiff
  | upPC : ProgramCounter -> frameDiff.

Inductive deltaState : Type :=
  | createFrame : Frame -> deltaState
  | updateFrame : frameDiff -> deltaState
  | deleteFrame : deltaState
  | upHeap : list (nat*arrOrObj) -> deltaState
  | upSHeap : SHeap -> deltaState
  | upInb : list (nat*nat) -> deltaState
  | upOutb : list (nat*nat) -> deltaState
  | upInc : Cursor -> deltaState
  | upOutc : Cursor -> deltaState
  | mkStuck : deltaState
  | mkHalt : deltaState.

Definition compFirst {A:Type} (t1 t2:(Location*A)) : bool :=
  match t1,t2 with
  | (l1,v1),(l2,v2) => (areEqualNum l1 l2)
  end.

Module Type ChangeStateType.
  Parameter state : Type.
  Parameter change : Type.
  Parameter changeFrame : Frame -> frameDiff -> Frame.
  Parameter mkChange : state -> change -> @Option state.
  Parameter mkChanges : state -> list change -> @Option state.
End ChangeStateType.

Module ChangeState <: ChangeStateType.
  Definition state := DVMState.
  Definition change := deltaState.
  Declare Module VLIST : ListType with Definition t1 := nat*Val.
  Fixpoint changeFrame (currf:Frame) (fd:frameDiff) : Frame :=
    match currf,fd with
    | (frm vals ml pc),(upPC pc2) => frm vals ml pc2
    | (frm vals ml pc),(upVals n v1) => match (VLIST.find (n,v1) compFirst vals) with
      | Some n' => frm (VLIST.set n' (n,v1) vals) ml pc
      | None => frm (VLIST.prep (n,v1) vals) ml pc
      end
    end.
  Declare Module ABLIST : ListType with Definition t1 := arrOrObj.
  Declare Module NLIST : ListType with Definition t1 := nat.
  Fixpoint mkChange (cst:state) (ch:change) : @Option state :=
    match cst with
    | dst frms h sh inb outb => match ch with
      | createFrame f => Some (dst (cons f frms) h sh inb outb)
      | updateFrame fd => match frms with
        | (cons f1 frem) => Some (dst (cons (changeFrame f1 fd) frem) h sh inb outb)
        | _ => None
        end
      | deleteFrame => match frms with
        | (cons f1 frem) => Some (dst frem h sh inb outb)
        | _ => None
        end
      | upHeap lst => Some (dst frms (ABLIST.setMany lst h) sh inb outb)
      | upSHeap sh' => Some (dst frms h sh' inb outb)
      | upInb lst => match inb with
        | (curs,lst') => Some (dst frms h sh (curs,(NLIST.setMany lst lst')) outb)
        end
      | upInc crs => match inb with
        | (curs,lst) => Some (dst frms h sh (crs,lst) outb)
        end
      | upOutb lst => match outb with
        | (curs,lst') => Some (dst frms h sh inb (curs,(NLIST.setMany lst lst')))
        end
      | upOutc crs => match outb with
        | (curs,lst) => Some (dst frms h sh inb (crs,lst))
        end
      | mkStuck => Some stuck
      | mkHalt => Some halt
      end
    | stuck => Some stuck
    | halt => Some halt
    end.
  Fixpoint mkChanges (cst:state) (chs:list change) : @Option state :=
    match chs with
    | nil => Some cst
    | (cons ch1 chrem) => match (mkChange cst ch1) with
      | (Some cst') => (mkChanges cst' chrem)
      | None => None
      end
    end.
End ChangeState.