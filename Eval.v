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
  Fixpoint evalLhs (exp:lhs) (st:DVMState) : @Option Val :=
    match exp,st with
    | (reg n),_ => evalReg n st
    | (acc n exp),dst _ h _ _ _ => match (evalReg n st) with
      | Some (ref (lRef lc)) => match (HP.get lc h),(evalRhs exp st) with
        | Some (ar (arr n' lst)),(Some (prim (int n''))) => (VLIST.get n'' lst)
        | _,_ => None
        end
      | _ => None
      end
    | (ifield n1 n2),(dst _ h _ _ _) => match (evalReg n1 st) with
      | Some (ref (lRef lc)) => match (HP.get lc h) with
        | Some (dob (obj n' lst)) => match (LVLIST.find (n2,(ref null)) compFirst lst) with
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