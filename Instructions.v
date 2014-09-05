Add LoadPath "D:\DVM".
Require Export Eval.
Require Export Example.
Require Export Method.
Require Export DType.

(**

* Enter The Dragon!

Welcome to the most crucial and intense part of whole implementation, in this module we provide functionality for
execution of each Instruction given a State and Program.

* InstructionType Signature

Its not much to discus about, just for abstarcting Instruction Module.

*)

Module Type InstructionType.
  Parameter inst : Type. (* ADT for Instrucion *)
  Parameter mthd : Type. (* ADT for Methods *)
  Parameter prg : Type. (* ADT for Programs*)
  Parameter toEval : inst -> list rhs.
  Parameter stepFix : DVMState -> prg -> @Option DVMState.
  (* Parameter evalWith : inst -> DVMState -> list ValOrRef -> list deltaState. *)
End InstructionType.

(**

* Instruction Module

*)

Module INSTRUCTION <: InstructionType.
(**

** Definitions
- ADT definitions
- A dummy functions of no use anymore

*)
  Definition inst := Instruction.
  Definition mthd := Method.
  Definition prg := Program.
  Fixpoint toEval (ins:inst) : list rhs :=
    match ins with
    | nop => nil
    | ret => nil
    | retTo _ => nil
    | invokes lst _ => lst
    | invokei r1 lst _ => lst
    | goto _ => nil
    | branch r1 _ r2 _ => (cons r1 (cons r2 nil))
    | move _ r1 => (cons r1 nil)
    | update r1 r2 => (cons r1 (cons r2 nil))
    | unary _ _ r1 => (cons r1 nil)
    | binaryArith _ r1 _ r2 => (cons r1 (cons r2 nil))
    | new _ _ => nil
    | newarr _ _ r1 => (cons r1 nil)
    | cast _ _ r1 => (cons r1 nil)
    | read _ => nil
    | print _ => nil
    | hlt => nil
    end.

(**

** evalNop : evaluate nop instruction

*)

  Definition evalNop (curr:DVMState) (p:prg) : deltaState :=
    match curr with
    | stuck => mkStuck
    | halt => mkHalt
    | dst nil _ _ _ _ => mkStuck
    | dst (cons (frm vals ml pc) frem) h sh bin bout => match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => updateFrame (upPC pc')
        | _ => mkStuck
        end
      | _ => mkStuck
      end
    end.

(**

** evalRet : evaluate ret instruction

*)

  Definition evalRet (curr:DVMState) (p:prg) : (list deltaState) :=
    match (EVAL.evalReg 201 curr),curr with
    | (Some x),(dst (cons f1 (cons (frm vals ml pc) frem)) h sh bin bout) => 
      match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => [deleteFrame ; updateFrame (upVals 201 x) ; updateFrame (upPC pc')]
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | None,(dst (cons f1 (cons (frm vals ml pc) frem)) h sh bin bout) => 
      match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => [deleteFrame ; updateFrame (upPC pc')]
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | _,halt => [mkHalt]
    | _,_ => [mkStuck]
    end.

(**

** evalRetTo : evaluate retTo instruction

*)

  Definition evalRetTo (curr:DVMState) (p:prg) (n:Location) : (list deltaState) :=
    match (EVAL.evalReg 201 curr),curr with
    | (Some x),(dst (cons f1 (cons (frm vals ml pc) frem)) h sh bin bout) => 
      match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => [deleteFrame ; updateFrame (upVals n x) ; updateFrame (upPC pc')]
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | None,(dst (cons f1 (cons (frm vals ml pc) frem)) h sh bin bout) => 
      match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => [deleteFrame ; updateFrame (upPC pc')]
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | _,halt => [mkHalt]
    | _,_ => [mkStuck]
    end.

(**

** evalInvokes : evaluate invokes instruction

*)

  Definition evalInvokes (curr:DVMState) (p:prg) (lst:list rhs) (ml:MethodLocation) : (list deltaState) :=
    match (Helpers.filter (Helpers.map lst (fun (x:rhs)=> (EVAL.evalRhs x curr))) isNone),(METHOD.firstPC ml p) with
    | nil,(Some pc) => cons (createFrame (frm [] ml pc)) (fastRev (map 
        (fun x:(nat*Val)=> match x with | (nx,vx) => updateFrame (upVals nx vx) end)
        (numberList 101 (map (fun (x:rhs)=> match (EVAL.evalRhs x curr) with
        | Some v1 => v1
        | _ => (ref null)
        end) (fastRev lst)))))
    | _,_ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

(**

** evalInvokei : evaluate invokei instruction
Register input takes object location for which method is called.

*)

  Definition evalInvokei (curr:DVMState) (p:prg) (lst:list rhs) (ml:MethodLocation) (n:nat) : (list deltaState) :=
    match (Helpers.filter (Helpers.map lst (fun (x:rhs)=> (EVAL.evalRhs x curr))) isNone),(METHOD.firstPC ml p),(EVAL.evalReg n curr) with
    | nil,(Some pc),(Some obv) => cons (createFrame (frm [] ml pc)) (cons (updateFrame (upVals 0 obv)) (fastRev (map 
        (fun x:(nat*Val)=> match x with | (nx,vx) => updateFrame (upVals nx vx) end)
        (numberList 101 (map (fun (x:rhs)=> match (EVAL.evalRhs x curr) with
        | Some v1 => v1
        | _ => (ref null)
        end) (fastRev lst))))))
    | _,_,_ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

(**

** evalGoto : evaluate goto instruction

*)

  Definition evalGoto (pc:ProgramCounter) : list deltaState :=
    [updateFrame (upPC pc)].

(**

** evalBranch : evaluate branch instruction

*)

  Definition evalBranch (l1 l2:rhs) (bc:BinaryCompOperator) (pc:ProgramCounter) (curr:DVMState) (p:prg) : list deltaState :=
    match (EVAL.evalRhs l1 curr),(EVAL.evalRhs l2 curr) with
    | Some (prim p1),Some (prim p2) => match bc with
      | beq => match (plus (PType.comp p1 p2) (PType.comp p2 p1))%nat with
        | 0 => [updateFrame (upPC pc)]
        | _ => [evalNop curr p]
        end
      | blt => match (PType.comp p2 p1) with
        | 0 => [evalNop curr p]
        | _ => [updateFrame (upPC pc)]
        end
      | bgt => match (PType.comp p1 p2) with
        | 0 => [evalNop curr p]
        | _ => [updateFrame (upPC pc)]
        end
      end
    | _,_ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

(**

** evalMove : evaluate move instruction

*)

  Definition evalMove (l1:rhs) (n:Register) (curr:DVMState) (p:prg) : list deltaState :=
    match (EVAL.evalRhs l1 curr) with
    | Some v1 => (cons (evalNop curr p) [updateFrame (upVals n v1)] )
    | _ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

  Declare Module HEAP : ListType with Definition t1 := arrOrObj.
  Declare Module VLIST : ListType with Definition t1 := Val.
  Declare Module FLIST : ListType with Definition t1 := FieldLocation*Val.

(**

** evalUpdate : evaluate update instruction

*)

  Definition evalUpdate (l1 l2:rhs) (curr:DVMState) (p:prg) : list deltaState :=
    match l1,(EVAL.evalRhs l2 curr),curr with
    | _,_,halt => [mkHalt]
    | _,_,stuck => [mkStuck]
    | (l (acc r1 r2)),(Some v1),(dst frms h sh inb outb) => match (EVAL.evalReg r1 curr),(EVAL.evalReg r2 curr) with
      | (Some (ref (lRef loc1))),(Some (prim p2)) => match (HEAP.get loc1 h),(PType.toNat p2) with
        | Some (ar (arr n1 vlst)),n2 => match (isle_num n2 n1) with
          | true => cons (evalNop curr p) [(upHeap [(loc1,(ar (arr n1 (VLIST.set n2 v1 vlst))))])]
          | _ => [mkStuck]
          end
        | _,_ => [mkStuck]
        end
      | _,_ => [mkStuck]
      end
    | (l (ifield r1 f1)),(Some v1),(dst frms h sh inb outb) => match (EVAL.evalReg r1 curr) with
      | Some (ref (lRef loc1)) => match (HEAP.get loc1 h) with
        | Some (dob (obj c1 c2 lst)) => match (FLIST.find (f1,(ref null)) compFirst lst) with
          | Some n1 => cons (evalNop curr p) [upHeap [(loc1,(dob (obj c1 c2 (FLIST.set n1 (f1,v1) lst))))]]
          | _ => [mkStuck]
          end
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | (l (sfield f1)),(Some v1),(dst frms h sh inb outb) => match (FLIST.find (f1,(ref null)) compFirst sh) with
      | Some n1 => cons (evalNop curr p) [upSHeap (FLIST.set n1 (f1,v1) sh)]
      | _ => [mkStuck]
      end
    | _,_,_ => [mkStuck]
    end.

(**

** evalUnary : evaluate unary instruction

*)

  Definition evalUnary (l1:rhs) (n:Register) (op:UnaryOperator) (curr:DVMState) (p:prg) : list deltaState :=
    match op,(EVAL.evalRhs l1 curr) with
    | unot,Some (prim p1) => match isle_num 1 (PType.toNat p1) with
      | true => evalMove (cs cfalse) n curr p
      | false => evalMove (cs ctrue) n curr p
      end
    | unot,Some (ref null) => evalMove (cs ctrue) n curr p
    | unot,Some _ => evalMove (cs cfalse) n curr p
    | unot,None => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

(**

** evalBinaryArith : evaluate binaryArith instruction

*)

  Definition evalBinaryArith (l1 l2:rhs) (n:Register) (op:BinaryArithOperator) (curr:DVMState) (p:prg) : list deltaState :=
    match curr with
    | halt => [mkHalt]
    | stuck => [mkStuck]
    | _ => match (EVAL.evalRhs l1 curr),(EVAL.evalRhs l2 curr) with
      | Some (prim p1),Some (prim p2) => match op with
        | badd => evalMove (cs (cnat ((PType.toNat p1) + (PType.toNat p2)))) n curr p
        | bsub => evalMove (cs (cnat ((PType.toNat p1) - (PType.toNat p2)))) n curr p
        | bmult => evalMove (cs (cnat ((PType.toNat p1) * (PType.toNat p2)))) n curr p
        | bdiv => evalMove (cs (cnat (div (PType.toNat p1) (PType.toNat p2)))) n curr p
        | bmod => evalMove (cs (cnat (mod (PType.toNat p1) (PType.toNat p2)))) n curr p
        end
      | _,_ => [mkStuck]
      end
    end.

  Declare Module HP : ListType with Definition t1 := arrOrObj.

(**

** evalNew : evaluate new instruction

*)

  Definition evalNew (n:Register) (cl:ClassLocation) (curr:DVMState) (p:prg) : list deltaState :=
    match curr with
    | stuck => [mkStuck]
    | halt => [mkHalt]
    | (dst _ h _ _ _) => match (TYPE.createObject p (r (c cl)) h) with
      | Some (addHeap vl1) => cons (evalNop curr p) (cons (addHeap vl1) (cons (updateFrame (upVals n (ref (lRef (HP.len h))))) nil) )
      | _ => [mkStuck]
      end
    end.

(**

** evalNewArray : evaluate newarr instruction

*)

  Definition evalNewArray (n:Register) (t:type) (l:rhs) (curr:DVMState) (p:prg) : list deltaState :=
    match curr,(EVAL.evalRhs l curr) with
    | stuck,_ => [mkStuck]
    | halt,_ => [mkHalt]
    | (dst _ h _ _ _),(Some v1) => match (EVAL.evalRhs l curr) with
      | Some (prim p1) => match (TYPE.createArray t (PType.toNat p1) h) with
        | Some (addHeap vl1) => cons (evalNop curr p) (cons (addHeap vl1) (cons (updateFrame (upVals n (ref (lRef (HP.len h))))) nil) )
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | _,_ => [mkStuck]
    end.

(**

** evalCast : evaluate cast instruction

*)

  Definition evalCast (n:Register) (t:type) (l:rhs) (curr:DVMState) (p:prg) : list deltaState :=
    match curr,(EVAL.evalRhs l curr) with
    | halt,_ => [mkHalt]
    | stuck,_ => [mkStuck]
    | (dst frms h sh inb outb),(Some v1) => match v1 with
      | (ref (lRef loc1)) => match (TYPE.cast p t loc1 h) with
        | Some (upHeap (cons (l1,ob1) nil)) => cons (evalNop curr p) (cons (upHeap (cons (l1,ob1) nil)) (cons (updateFrame (upVals n (ref (lRef l1)))) nil))
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    | _,_ => [mkStuck]
    end.

  Declare Module NLIST:ListType with Definition t1:=nat.

(**

** evalRead : evaluate read instruction

*)

  Definition evalRead (n:Register) (curr:DVMState) (p:prg) : list deltaState :=
    match curr with
    | halt => [mkHalt]
    | stuck => [mkStuck]
    | (dst frms h sh (crs,lst) outb) => match (NLIST.get crs lst) with
      | Some num => cons (evalNop curr p) (cons (upInc (S crs)) (cons (updateFrame (upVals n (prim (int num)))) nil))
      | None => [mkStuck]
      end
    end.

(**

** evalWrite : evaluate print instruction

*)

  Definition evalWrite (r1:rhs) (curr:DVMState) (p:prg) : list deltaState :=
    match curr,(EVAL.evalRhs r1 curr) with
    | halt,_ => [mkHalt]
    | stuck,_ => [mkStuck]
    | (dst frms h sh inb (crs,lst)),(Some (prim p1)) => cons (evalNop curr p) [(addOutb (PType.toNat p1))]
    | _,_ => [mkStuck]
    end.

(**

** evalInst : evaluate any instruction

*)

  Definition evalInst (inst:Instruction) (curr:DVMState) (p:prg) : list deltaState :=
    match inst with
    | nop => [evalNop curr p]
    | ret => evalRet curr p
    | retTo r1 => evalRetTo curr p r1
    | invokes lst ml => evalInvokes curr p lst ml
    | invokei r1 lst ml => evalInvokei curr p lst ml r1
    | goto pc => evalGoto pc
    | branch r1 bcmp r2 pc => evalBranch r1 r2 bcmp pc curr p
    | move r1 r2 => evalMove r2 r1 curr p
    | update r1 r2 => evalUpdate r1 r2 curr p
    | unary n1 uop r1 => evalUnary r1 n1 uop curr p
    | binaryArith n1 r1 binop r2 => evalBinaryArith r1 r2 n1 binop curr p
    | new n1 cl => evalNew n1 cl curr p
    | newarr n1 t1 r1 => evalNewArray n1 t1 r1 curr p
    | cast n1 t1 r1 => evalCast n1 t1 r1 curr p
    | read n1 => evalRead n1 curr p
    | print r1 => evalWrite r1 curr p
    | hlt => [mkHalt]
    end.

(**

** C.I.P. : Compute In Peace

With execution defined, we can now write fixpoints to compute a Program

*)

  Definition getCurrInstruction (curr:DVMState) (p:prg) : @Option Instruction :=
    match curr with
    | (dst (cons (frm _ ml pc) _) _ _ _ _) => match (METHOD.getMethod ml p) with
      | Some md => METHOD.getInstAt pc md
      | None => None
      end
    | halt => Some hlt
    | _ => None
    end.

  Definition stepWith (i:Instruction) (curr:DVMState) (p:prg) : @Option DVMState := (ChangeState.mkChanges curr (evalInst i curr p)).

  Definition stepFix (curr:DVMState) (p:prg) : @Option DVMState :=
    match (getCurrInstruction curr p) with
    | Some ins => (ChangeState.mkChanges curr (evalInst ins curr p))
    | None => None
    end.

  Fixpoint multiStepFix (n:nat) (curr:DVMState) (p:prg) : @Option DVMState :=
    match n with
    | 0 => (stepFix curr p)
    | S n' => match (stepFix curr p) with
      | Some st => (multiStepFix n' st p)
      | None => None
      end
    end.

  Compute (multiStepFix 100 currState p).

End INSTRUCTION.