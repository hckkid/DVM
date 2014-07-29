Add LoadPath "D:\DVM".
Require Export Instructions.

Declare Module RLIST : ListType with Definition t1 := nat*Val.
Declare Module HP : ListType with Definition t1 := arrOrObj.
Declare Module VLIST : ListType with Definition t1 := Val.
Declare Module LVLIST : ListType with Definition t1 := (FieldLocation*Val).
Declare Module SVLIST : ListType with Definition t1 := (FieldLocation*Val).

Inductive consistentNop : DVMState -> Program -> Prop :=
  | consistencyNopDst : forall (p:Program) (vals:list (nat*Val)) (ml:MethodLocation) (pc:ProgramCounter) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (md:Method), 
                        METHOD.getMethod ml p = Some md ->
                        METHOD.getNextPC pc md = Some pc ->
                        consistentNop (dst (cons (frm vals ml pc) frms) h sh inb outb) p
  | consistencyNopHalt : forall (p:Program), consistentNop halt p.

Inductive consistentEvalReg : nat -> DVMState -> Prop :=
  | consistencyReg : forall (n n':nat) (vals:list (nat*Val)) (ml:MethodLocation) (pc:ProgramCounter) (frem:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                     RLIST.findRel (n,ref null) compFirst vals (Some n') ->
                     consistentEvalReg n (dst (cons (frm vals ml pc) frem) h sh inb outb).

Inductive consistentRet : DVMState -> Program -> Prop :=