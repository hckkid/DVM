Add LoadPath "D:\DVM".
Require Export DvmState.
Require Export Program.

Module Type EVALTYPE.
  Parameter evalReg : nat -> DVMState -> @Option Val.
  Parameter evalLhs : lhs -> DVMState -> @Option Val.
  Parameter evalRhs : rhs -> DVMState -> @Option Val.
End EVALTYPE.

Module EVAL <: EVALTYPE.
  Declare Module RLIST : ListType with Definition t1 := nat*Val.
  Declare Module HP : ListType with Definition t1 := arrOrObj.
  Declare Module VLIST : ListType with Definition t1 := Val.
  Declare Module LVLIST : ListType with Definition t1 := (FieldLocation*Val).
  Declare Module SVLIST : ListType with Definition t1 := (FieldLocation*Val).

  Fixpoint evalReg (n:nat) (st:DVMState) : @Option Val :=
    match st with
    | dst nil _ _ _ _ => None
    | dst (cons (frm lst m pc) frem) _ _ _ _ => match (RLIST.find (n,(ref null)) compFirst lst) with
      | (Some n') => match (RLIST.get n' lst) with
        | (Some (_,x)) => Some x
        | None => None
        end
      | None => None
      end
    | stuck => None
    | halt => None
    end.

  Inductive evalRegRel : nat -> DVMState -> @Option Val -> Prop :=
    | nilEvalRegRel : forall (n:nat) (h:Heap) (sh:SHeap) (inb outb:Buffer), evalRegRel n (dst nil h sh inb outb) None
    | someSomeEvalRegRel : forall (n n' n'':nat) (x:Val) (frem:list Frame) (lst:list (nat*Val)) (m:MethodLocation) (pc:ProgramCounter) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                      RLIST.findRel (n,(ref null)) compFirst lst (Some n') ->
                      RLIST.getRel n' lst (Some (n'',x)) ->
                      evalRegRel n (dst (cons (frm lst m pc) frem) h sh inb outb) (Some x)
    | someNoneEvalRegRel : forall (n n':nat) (frem:list Frame) (lst:list (nat*Val)) (m:MethodLocation) (pc:ProgramCounter) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                      RLIST.findRel (n,(ref null)) compFirst lst (Some n') ->
                      RLIST.getRel n' lst None ->
                      evalRegRel n (dst (cons (frm lst m pc) frem) h sh inb outb) None
    | noneEvalRegRel : forall (n:nat) (frem:list Frame) (lst:list (nat*Val)) (m:MethodLocation) (pc:ProgramCounter) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                      RLIST.findRel (n,(ref null)) compFirst lst None ->
                      evalRegRel n (dst (cons (frm lst m pc) frem) h sh inb outb) None
    | stuckEvalRegRel : forall (n:nat), evalRegRel n stuck None
    | haltEvalRegRel : forall (n:nat), evalRegRel n halt None.

  Theorem evalRegRelEq : forall (n:nat) (st:DVMState) (v1:@Option Val), evalReg n st = v1 <-> evalRegRel n st v1.
  Proof.
    split; intro.
    destruct st; simpl in H; subst; simpl; try (destruct n; simpl; econstructor). 
    destruct frms; simpl.
      destruct n; simpl; econstructor.
      destruct n; simpl; destruct f; simpl.
      remember (RLIST.find (0, ref null) compFirst vals) as fres; destruct fres; symmetry in Heqfres;
      apply RLIST.findRelEq in Heqfres; try constructor; auto.
      remember (RLIST.get n vals) as gres; destruct gres; symmetry in Heqgres; apply RLIST.getRelEq in Heqgres.
      destruct t.

  Fixpoint evalLhs (exp:lhs) (st:DVMState) : @Option Val :=
    match exp,st with
    | (reg n),_ => evalReg n st
    | (acc n n2),dst _ h _ _ _ => match (evalReg n st) with
      | Some (ref (lRef lc)) => match (HP.get lc h),(evalReg n2 st) with
        | Some (ar (arr n' lst)),(Some (prim (int n''))) => (VLIST.get n'' lst)
        | _,_ => None
        end
      | _ => None
      end
    | (ifield n1 n2),(dst _ h _ _ _) => match (evalReg n1 st) with
      | Some (ref (lRef lc)) => match (HP.get lc h) with
        | Some (dob (obj n' n'' lst)) => match (LVLIST.find (n2,(ref null)) compFirst lst) with
          | Some n3 => match (LVLIST.get n3 lst) with
            | Some (n',vl') => Some vl'
            | None => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | (sfield n),(dst _ _ sh _ _) => match (SVLIST.find (n,(ref null)) compFirst sh) with
      | Some n2 => match (SVLIST.get n2 sh) with
        | Some (n3,v') => Some v'
        | None => None
        end
      | None => None
      end
    | _ , _ => None
    end
  with evalRhs (exp:rhs) (st:DVMState) : @Option Val :=
    match exp with
    | (l lhs1) => (evalLhs lhs1 st)
    | (cs cnst) => match cnst with
      | cnat n => Some (prim (int n))
      | ctrue => Some (prim (boolean 1))
      | cfalse => Some (prim (boolean 0))
      | cnull => Some (ref null)
      end
    end.
End EVAL.