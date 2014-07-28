Add LoadPath "D:\DVM".
Require Export Eval.
Require Export Example.
Require Export Method.

Module Type InstructionType.
  Parameter inst : Type. (* ADT for Instrucion *)
  Parameter mthd : Type. (* ADT for Methods *)
  Parameter prg : Type. (* ADT for Programs*)
  Parameter toEval : inst -> list rhs.
  Parameter evalNop : DVMState -> prg -> list deltaState.
  (* Parameter evalWith : inst -> DVMState -> list ValOrRef -> list deltaState. *)
End InstructionType.

Module INSTRUCTION <: InstructionType.
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
    | unaryArith _ _ r1 => (cons r1 nil)
    | binaryArith _ r1 _ r2 => (cons r1 (cons r2 nil))
    | new _ _ => nil
    | newarr _ _ r1 => (cons r1 nil)
    | cast _ _ r1 => (cons r1 nil)
    | read _ _ => nil
    | print _ r1 => (cons r1 nil)
    end.

  Definition evalNop (curr:DVMState) (p:prg) : list deltaState :=
    match curr with
    | stuck => [mkStuck]
    | halt => [mkHalt]
    | dst nil _ _ _ _ => [mkStuck]
    | dst (cons (frm vals ml pc) frem) h sh bin bout => match (METHOD.getMethod ml p) with
      | Some md => match (METHOD.getNextPC pc md) with
        | Some pc' => [updateFrame (upPC pc')]
        | _ => [mkStuck]
        end
      | _ => [mkStuck]
      end
    end.

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
    | _,halt => [mkHalt]
    | _,_ => [mkStuck]
    end.

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
    | _,halt => [mkHalt]
    | _,_ => [mkStuck]
    end.

  Definition evalInvokes (curr:DVMState) (p:prg) (lst:list rhs) (ml:MethodLocation) : (list deltaState) :=
    match (filter isNone (map (fun (x:rhs)=> (EVAL.evalRhs x curr)) lst)),(METHOD.firstPC ml p) with
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

  Definition evalInvokei (curr:DVMState) (p:prg) (lst:list rhs) (ml:MethodLocation) (n:nat) : (list deltaState) :=
    match (filter isNone (map (fun (x:rhs)=> (EVAL.evalRhs x curr)) lst)),(METHOD.firstPC ml p),(EVAL.evalReg n curr) with
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

  Definition evalGoto (pc:ProgramCounter) : list deltaState :=
    [updateFrame (upPC pc)].

  Definition evalBranch (l1 l2:rhs) (bc:BinaryCompOperator) (pc:ProgramCounter) (curr:DVMState) (p:prg) : list deltaState :=
    match (EVAL.evalRhs l1 curr),(EVAL.evalRhs l1 curr) with
    | Some (prim p1),Some (prim p2) => match bc with
      | beq => match ((PType.comp p1 p2)+(PType.comp p2 p1))%nat with
        | 0 => [updateFrame (upPC pc)]
        | _ => (evalNop curr p)
        end
      | blt => match (PType.comp p2 p1) with
        | 0 => (evalNop curr p)
        | _ => [updateFrame (upPC pc)]
        end
      | bgt => match (PType.comp p1 p2) with
        | 0 => (evalNop curr p)
        | _ => [updateFrame (upPC pc)]
        end
      end
    | _,_ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

  Definition move (l1:rhs) (n:Register) (curr:DVMState) (p:prg) : list deltaState :=
    match (EVAL.evalRhs l1 curr) with
    | Some v1 => [updateFrame (upVals n v1)]
    | _ => match curr with
      | halt => [mkHalt]
      | _ => [mkStuck]
      end
    end.

End INSTRUCTION.