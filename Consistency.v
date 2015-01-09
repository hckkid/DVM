Require Export Instructions.

(**

* Overview

This module creates consistency relations to check different kinds of consistencies in between heap,instruction,
frames, program etc. Our progress property makes use of instruction being consistent with state and program to
state that given instruction will definitely go into some next non stuck state or not.

*)

(**

* Instrcution consistency

*)

Inductive consistentNop : DVMState -> Program -> Prop :=
  | consistencyNopDst : forall (p:Program) (vals:list (nat*Val)) (ml:MethodLocation) (pc:ProgramCounter) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (md:Method), 
                        METHOD.getMethod ml p = Some md ->
                        METHOD.getNextPC pc md = Some pc ->
                        consistentNop (dst (cons (frm vals ml pc) frms) h sh inb outb) p
  | consistencyNopHalt : forall (p:Program), consistentNop halt p.

Inductive consistentEvalReg : nat -> DVMState -> Prop :=
  | consistencyReg : forall (n n':nat) (vals:list (nat*Val)) (ml:MethodLocation) (pc:ProgramCounter) (frem:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                     EVAL.RLIST.findRel (n,ref null) compFirst vals (Some n') ->
                     consistentEvalReg n (dst (cons (frm vals ml pc) frem) h sh inb outb).

Inductive consistentRet : DVMState -> Program -> Prop :=
  | consistencyRet : forall (p:Program) (f:Frame) (vals:list (nat*Val)) (ml:MethodLocation) (pc pc':ProgramCounter) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (md:Method),
                     METHOD.getMethod ml p = Some md ->
                     METHOD.getNextPC pc md = Some pc' ->
                     consistentRet (dst (cons f (cons (frm vals ml pc) frms)) h sh inb outb) p
  | consistentRetHalt : forall (p:Program), consistentRet halt p.

Inductive consistentEvalLhs : lhs -> DVMState -> Prop :=
  | consistencyRegLhs : forall (n:nat) (st:DVMState),
                     consistentEvalReg n st ->
                     consistentEvalLhs (reg n) st
  | consistencyAccLhs : forall (frms:list Frame) (h:Heap) (sh:SHeap)  (inb outb:Buffer) (lc:Location) (n n2 n' n'': nat) (lst:list Val) (p1:Prim),
                     EVAL.evalRegRel n (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                     EVAL.HP.getRel lc h (Some (ar (arr n' lst))) ->
                     EVAL.evalRegRel n2 (dst frms h sh inb outb) (Some (prim p1)) ->
                     EVAL.VLIST.len lst = n' ->
                     PType.toNatRel p1 n'' ->
                     n'' < n' ->
                     consistentEvalLhs (acc n n2) (dst frms h sh inb outb)
  | consistencyIfieldLhs : forall (frms:list Frame) (h:Heap) (sh:SHeap)  (inb outb:Buffer) (lc:Location) (n n2 n3 n' n'': nat) (lst:list (FieldLocation*Val)) (vl:FieldLocation*Val),
                     EVAL.evalRegRel n (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                     EVAL.HP.getRel lc h (Some (dob (obj n' n'' lst))) ->
                     EVAL.LVLIST.findRel (n2,(ref null)) compFirst lst (Some n3) ->
                     EVAL.LVLIST.getRel n3 lst (Some vl) ->
                     consistentEvalLhs (ifield n n2) (dst frms h sh inb outb)
  | consistencySfieldLhs : forall (frms:list Frame) (h:Heap) (sh:SHeap)  (inb outb:Buffer) (lc:Location) (n n2: nat) (vl:FieldLocation*Val),
                     EVAL.SVLIST.findRel (n,(ref null)) compFirst sh (Some n2) ->
                     EVAL.SVLIST.getRel n2 sh (Some vl) ->
                     consistentEvalLhs (sfield n) (dst frms h sh inb outb).

Inductive consistentEvalRhs : rhs -> DVMState -> Prop :=
  | consistencyLhsRhs : forall (l1:lhs) (st:DVMState), consistentEvalLhs l1 st ->
                     consistentEvalRhs (l l1) st
  | consistencyConstantRhs : forall (cns:Constant) (st:DVMState), consistentEvalRhs (cs cns) st.

Inductive consistentInvokes : DVMState -> Program -> (list rhs) -> MethodLocation -> Prop :=
  | consistencyInvokes : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (lst:list rhs) (pc:ProgramCounter) (ml:MethodLocation),
                     METHOD.firstPC ml p = (Some pc) ->
                     forAllList lst (fun x:rhs => (consistentEvalRhs x (dst frms h sh inb outb))) ->
                     consistentInvokes (dst frms h sh inb outb) p lst ml
  | consistentInvokesHalt : forall (p:Program) (lst:list rhs) (ml:MethodLocation),
                     consistentInvokes halt p lst ml.

Inductive consistentInvokei : DVMState -> Program -> (list rhs) -> MethodLocation -> nat -> Prop :=
  | consistencyInvokei : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (lst:list rhs) (pc:ProgramCounter) (ml:MethodLocation) (n:nat),
                     METHOD.firstPC ml p = (Some pc) ->
                     forAllList lst (fun x:rhs => (consistentEvalRhs x (dst frms h sh inb outb))) ->
                     consistentEvalReg n (dst frms h sh inb outb) ->
                     consistentInvokei (dst frms h sh inb outb) p lst ml n
  | consistentInvokeiHalt : forall (p:Program) (lst:list rhs) (ml:MethodLocation) (n:nat),
                     consistentInvokei halt p lst ml n.

Inductive consistentGoto : DVMState -> Program -> ProgramCounter -> Prop :=
  | consistencyGoto : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (pc:ProgramCounter),
                     consistentGoto (dst frms h sh inb outb) p pc
  | consistencyGotoHalt : forall (p:Program) (pc:ProgramCounter),
                     consistentGoto halt p pc.

Inductive consistentBranch : DVMState -> Program -> rhs -> rhs -> BinaryCompOperator -> ProgramCounter -> Prop :=
  | consistencyBranch : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (pc:ProgramCounter) (r1 r2:rhs) (bcomp:BinaryCompOperator) (p1 p2:Prim),
                     EVAL.evalRhsRel r1 (dst frms h sh inb outb) (Some (prim p1)) ->
                     EVAL.evalRhsRel r2 (dst frms h sh inb outb) (Some (prim p2)) ->
                     consistentBranch (dst frms h sh inb outb) p r1 r2 bcomp pc
  | consistencyBranchHalt : forall (p:Program) (pc:ProgramCounter) (r1 r2:rhs) (bcomp:BinaryCompOperator),
                     consistentBranch halt p r1 r2 bcomp pc.

Inductive consistentMove : DVMState -> Program -> Register -> rhs -> Prop :=
  | consistencyMove : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (n:Register) (r1:rhs),
                     consistentEvalRhs r1 (dst frms h sh inb outb) ->
                     consistentMove (dst frms h sh inb outb) p n r1
  | consistencyMoveHalt : forall (p:Program) (n:Register) (r1:rhs), consistentMove halt p n r1.

Inductive consistentUpdate : DVMState -> Program -> rhs -> rhs -> Prop :=
  | consistencyAccUpdate : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (n1 n2:Register) (n3 n4:nat) (r2:rhs) (loc1:Location) (p2:Prim) (vlst:list Val),
                     consistentEvalRhs r2 (dst frms h sh inb outb) ->
                     EVAL.evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef loc1))) ->
                     EVAL.evalRegRel n2 (dst frms h sh inb outb) (Some (prim p2)) ->
                     EVAL.HP.getRel loc1 h (Some (ar (arr n3 vlst))) ->
                     PType.toNatRel p2 n4 ->
                     n4 < (S n3) ->
                     consistentUpdate (dst frms h sh inb outb) p (l (acc n1 n2)) r2
  | consistencyIfieldUpdate : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (n1:Register) (n2:nat) (f1:FieldLocation) (r2:rhs) (c1 c2:ClassLocation) (loc1:Location) (lst:list (FieldLocation*Val)),
                     consistentEvalRhs r2 (dst frms h sh inb outb) ->
                     EVAL.evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef loc1))) ->
                     EVAL.HP.getRel loc1 h (Some (dob (obj c1 c2 lst))) ->
                     INSTRUCTION.FLIST.findRel (f1,(ref null)) compFirst lst (Some n2) ->
                     consistentUpdate (dst frms h sh inb outb) p (l (ifield n1 f1)) r2
  | consistencySfieldUpdate : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (f1:FieldLocation) (n:nat) (r2:rhs),
                     consistentEvalRhs r2 (dst frms h sh inb outb) ->
                     INSTRUCTION.FLIST.findRel (f1,(ref null)) compFirst sh (Some n) ->
                     consistentUpdate (dst frms h sh inb outb) p (l (sfield f1)) r2
  | consistencyUpdateHalt : forall (p:Program) (r1 r2:rhs), consistentUpdate halt p r1 r2.

Inductive consistentUnary : DVMState -> Program -> Register -> rhs -> UnaryOperator -> Prop :=
  | consistencyUnot : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (r1:rhs) (n:Register),
                     consistentEvalRhs r1 (dst frms h sh inb outb) ->
                     consistentUnary (dst frms h sh inb outb) p n r1 unot
  | consistencyHalt : forall (p:Program) (r1:rhs) (n:Register) (uop:UnaryOperator),
                     consistentUnary halt p n r1 uop.

Inductive consistentBinaryArith : DVMState -> Program -> Register -> rhs -> rhs -> BinaryArithOperator -> Prop :=
  | consistencyPrimPrimBinaryArith : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (r1 r2:rhs) (n:Register) (p1 p2:Prim) (binop:BinaryArithOperator),
                     EVAL.evalRhsRel r1 (dst frms h sh inb outb) (Some (prim p1)) ->
                     EVAL.evalRhsRel r2 (dst frms h sh inb outb) (Some (prim p2)) ->
                     consistentBinaryArith (dst frms h sh inb outb) p n r1 r2 binop
  | consistencyBinaryArithHalt : forall (p:Program) (r1 r2:rhs) (n:Register) (binop:BinaryArithOperator),
                     consistentBinaryArith halt p n r1 r2 binop.

Inductive consistentNew : DVMState -> Program -> Register -> ClassLocation -> Prop :=
  | consistencyNew : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (cl:ClassLocation) (vl1:arrOrObj) (n:Register),
                     (TYPE.createObject p (r (c cl)) h) = Some (addHeap vl1) ->
                     consistentNew (dst frms h sh inb outb) p n cl
  | consistencyNewHalt : forall (p:Program) (n:Register) (cl:ClassLocation),
                     consistentNew halt p n cl.

Inductive consistentNewArray : DVMState -> Program -> Register -> type -> rhs -> Prop :=
  | consistencyNewArray : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (ty:type) (r1:rhs) (vl1:arrOrObj) (n:Register) (p1:Prim) (n':nat),
                     EVAL.evalRhsRel r1 (dst frms h sh inb outb) (Some (prim p1)) ->
                     PType.toNatRel p1 n' ->
                     (TYPE.createArray ty n' h) = Some (addHeap vl1) ->
                     consistentNewArray (dst frms h sh inb outb) p n ty r1
  | consistencyNewArrayHalt : forall (p:Program) (n:Register) (ty:type) (r1:rhs),
                     consistentNewArray halt p n ty r1.

Inductive consistentRead : DVMState -> Program -> Register -> Prop :=
  | consistencyRead : forall (frms:list Frame) (h:Heap) (sh:SHeap) (crs:Cursor) (lst:list nat) (outb:Buffer) (p:Program) (n:Register) (n':nat),
                     INSTRUCTION.NLIST.getRel crs lst (Some n') ->
                     consistentRead (dst frms h sh (crs,lst) outb) p n
  | consistencyReadHalt : forall (p:Program) (n:Register),
                     consistentRead halt p n.

Inductive consistentWrite : DVMState -> Program -> rhs -> Prop :=
  | consistencyWrite : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (r1:rhs) (p1:Prim),
                     EVAL.evalRhsRel r1 (dst frms h sh inb outb) (Some (prim p1)) ->
                     consistentWrite (dst frms h sh inb outb) p r1
  | consistencyWriteHalt : forall (p:Program) (r1:rhs),
                     consistentWrite halt p r1.

Inductive consistentCast : DVMState -> Program -> Register -> type -> rhs -> Prop :=
  | consistencyCast : forall (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (p:Program) (r1:rhs) (loc1:Location) (ty:type) (n:Register) (lst:list (Location*arrOrObj)),
                     EVAL.evalRhsRel r1 (dst frms h sh inb outb) (Some (ref (lRef loc1))) ->
                     TYPE.cast p ty loc1 h = Some (upHeap lst) ->
                     consistentCast (dst frms h sh inb outb) p n ty r1
  | consistencyCastHalt : forall (p:Program) (n:Register) (ty:type) (r1:rhs),
                     consistentCast halt p n ty r1.

Inductive consistentInst : Instruction -> DVMState -> Program -> Prop :=
  | consistentInstNop : forall (st:DVMState) (p:Program), 
                     consistentNop st p -> 
                     consistentInst nop st p
  | consistentInstRet : forall (st:DVMState) (p:Program),
                     consistentRet st p ->
                     consistentInst ret st p
  | consistentInstRetTo : forall (st:DVMState) (p:Program) (n:Register),
                     consistentRet st p ->
                     consistentInst (retTo n) st p
  | consistentInstInvokes : forall (st:DVMState) (p:Program) (lst:list rhs) (ml:MethodLocation),
                     consistentInvokes st p lst ml ->
                     consistentInst (invokes lst ml) st p
  | consistentInstInvokei : forall (st:DVMState) (p:Program) (lst:list rhs) (ml:MethodLocation) (n:Register),
                     consistentInvokei st p lst ml n ->
                     consistentInst (invokei n lst ml) st p
  | consistentInstGoto : forall (st:DVMState) (p:Program) (pc:ProgramCounter),
                     consistentGoto st p pc ->
                     consistentInst (goto pc) st p
  | consistentInstBranch : forall (st:DVMState) (p:Program) (r1 r2:rhs) (bcmp:BinaryCompOperator) (pc:ProgramCounter),
                     consistentBranch st p r1 r2 bcmp pc ->
                     consistentInst (branch r1 bcmp r2 pc) st p
  | consistentInstMove : forall (st:DVMState) (p:Program) (n:Register) (r1:rhs),
                     consistentMove st p n r1 ->
                     consistentInst (move n r1) st p
  | consistentInstUpdate : forall (st:DVMState) (p:Program) (r1 r2:rhs),
                     consistentUpdate st p r1 r2 ->
                     consistentInst (update r1 r2) st p
  | consistentInstUnary : forall (st:DVMState) (p:Program) (n:Register) (uop:UnaryOperator) (r1:rhs),
                     consistentUnary st p n r1 uop ->
                     consistentInst (unary n uop r1) st p
  | consistentInstBinaryArith : forall (st:DVMState) (p:Program) (n:Register) (binop:BinaryArithOperator) (r1 r2:rhs),
                     consistentBinaryArith st p n r1 r2 binop ->
                     consistentInst (binaryArith n r1 binop r2) st p
  | consistentInstNew : forall (st:DVMState) (p:Program) (n:Register) (cl:ClassLocation),
                     consistentNew st p n cl ->
                     consistentInst (new n cl) st p
  | consistentInstNewArray : forall (st:DVMState) (p:Program) (n:Register) (ty:type) (r1:rhs),
                     consistentNewArray st p n ty r1 ->
                     consistentInst (newarr n ty r1) st p
  | consistentInstCast : forall (st:DVMState) (p:Program) (n:Register) (ty:type) (r1:rhs),
                     consistentCast st p n ty r1 ->
                     consistentInst (cast n ty r1) st p
  | consistentInstRead : forall (st:DVMState) (p:Program) (n:Register),
                     consistentRead st p n ->
                     consistentInst (read n) st p
  | consistentInstWrite : forall (st:DVMState) (p:Program) (r1:rhs),
                     consistentWrite st p r1 ->
                     consistentInst (print r1) st p.