Require Export DvmState.
Require Export Program.

(**

* Overview

This Module implements functionality to evaluate simple expressions that occur in CoqDVM instruction provided current state

* EVALTYPE signature

Here we have just three function prototypes
- evalReg : evaluates value of a register
- evalLhs : evaluates value of lhs expression
- evalRhs : evaluates value of rhs expression

*)


Module Type EVALTYPE.
  Parameter evalReg : nat -> DVMState -> @Option Val.
  Parameter evalLhs : lhs -> DVMState -> @Option Val.
  Parameter evalRhs : rhs -> DVMState -> @Option Val.
End EVALTYPE.

(**

* EVAL module

*)

Module EVAL <: EVALTYPE.

(**

List Based Declarions to be used later.

*)
  Declare Module RLIST : ListType with Definition t1 := nat*Val.
  Declare Module HP : ListType with Definition t1 := arrOrObj.
  Declare Module VLIST : ListType with Definition t1 := Val.
  Declare Module LVLIST : ListType with Definition t1 := (FieldLocation*Val).
  Declare Module SVLIST : ListType with Definition t1 := (FieldLocation*Val).

(**

** evalReg : Evaluates Register

*)

  Fixpoint evalReg (n:nat) (st:DVMState) : @Option Val :=
    match st with
    | dst nil h sh inb outb => None
    | dst (cons (frm lst m pc) frem) h sh inb outb => match (RLIST.find (n,(ref null)) compFirst lst) with
      | (Some n') => match (RLIST.get n' lst) with
        | (Some (z,x)) => Some x
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
      destruct t. econstructor. eapply Heqfres. eapply Heqgres.
      eapply someNoneEvalRegRel. eapply Heqfres. apply Heqgres.
      remember (RLIST.find ((S n), ref null) compFirst vals) as fres; destruct fres; symmetry in Heqfres;
      apply RLIST.findRelEq in Heqfres; try constructor; auto.
      remember (RLIST.get n0 vals) as gres; destruct gres; symmetry in Heqgres; apply RLIST.getRelEq in Heqgres.
      destruct t. econstructor. eapply Heqfres. eapply Heqgres.
      eapply someNoneEvalRegRel. eapply Heqfres. apply Heqgres.
    inversion H; subst; destruct n; simpl; try reflexivity;
      try (apply RLIST.findRelEq in H0; rewrite H0; try reflexivity; apply RLIST.getRelEq in H1; rewrite H1; reflexivity).
  Qed.

(**

** evalLhs : Evaluates lhs expressions

*)

  Definition evalLhs (exp:lhs) (st:DVMState) : @Option Val :=
    match exp,st with
    | (reg n),x => evalReg n st
    | (acc n n2),dst frms h sh inb outb => match (evalReg n st) with
      | Some (ref (lRef lc)) => match (HP.get lc h),(evalReg n2 st) with
        | Some (ar (arr n' lst)),(Some (prim p1)) => (VLIST.get (PType.toNat p1) lst)
        | x,y => None
        end
      | x => None
      end
    | (ifield n1 n2),(dst frms h sh inb outb) => match (evalReg n1 st) with
      | Some (ref (lRef lc)) => match (HP.get lc h) with
        | Some (dob (obj n' n'' lst)) => match (LVLIST.find (n2,(ref null)) compFirst lst) with
          | Some n3 => match (LVLIST.get n3 lst) with
            | Some (n',vl') => Some vl'
            | None => None
            end
          | x => None
          end
        | x => None
        end
      | x => None
      end
    | (sfield n),(dst frms h sh inb outb) => match (SVLIST.find (n,(ref null)) compFirst sh) with
      | Some n2 => match (SVLIST.get n2 sh) with
        | Some (n3,v') => Some v'
        | None => None
        end
      | None => None
      end
    | x , y => None
    end.

  Inductive evalLhsRel : lhs -> DVMState -> @Option Val -> Prop :=
    | regEvalLhsRel : forall (n:nat) (st:DVMState) (v:@Option Val), evalRegRel n st v -> evalLhsRel (reg n) st v
    | noneFirstAccEvalLhsRel : forall (n n2:nat) (st:DVMState), evalRegRel n st None -> evalLhsRel (acc n n2) st None
    | somePrimFirstAccEvalLhsRel : forall (n n2:nat) (p:Prim) (st:DVMState), evalRegRel n st (Some (prim p)) -> evalLhsRel (acc n n2) st None
    | someNullFirstAccEvalLhsRel : forall (n n2:nat) (st:DVMState), evalRegRel n st (Some (ref null)) -> evalLhsRel (acc n n2) st None
    | noneSecondAccEvalLhsRel : forall (n n2:nat) (st:DVMState), evalRegRel n2 st None -> evalLhsRel (acc n n2) st None
    | someRefSecondAccEvalLhsRel : forall (n n2:nat) (r:Ref) (st:DVMState), evalRegRel n2 st (Some (ref r)) -> evalLhsRel (acc n n2) st None
    | someNoneAccEvalLhsRel : forall (n n2:nat) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h None ->
                              evalLhsRel (acc n n2) (dst frms h sh inb outb) None
    | someSomeDobAccEvalLhsRel : forall (n n2:nat) (lc:Location) (object:Object) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob object)) ->
                              evalLhsRel (acc n n2) (dst frms h sh inb outb) None
    | someSomeArAccEvalLhsRel : forall (n n1 n2 n':nat) (lc:Location) (p1:Prim) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (v:@Option Val) (lst:list Val),
                              evalRegRel n (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (ar (arr n' lst))) ->
                              evalRegRel n2 (dst frms h sh inb outb) (Some (prim p1)) ->
                              PType.toNatRel p1 n1 ->
                              VLIST.getRel n1 lst v ->
                              evalLhsRel (acc n n2) (dst frms h sh inb outb) v
    | noneFirstIfieldEvalLhsRel : forall (n1 n2:nat) (st:DVMState), evalRegRel n1 st None -> evalLhsRel (ifield n1 n2) st None
    | somePrimFirstIfieldEvalLhsRel : forall (n1 n2:nat) (st:DVMState) (p1:Prim), evalRegRel n1 st (Some (prim p1)) -> evalLhsRel (ifield n1 n2) st None
    | someNullFirstIfieldEvalLhsRel : forall (n1 n2:nat) (st:DVMState), evalRegRel n1 st (Some (ref null)) -> evalLhsRel (ifield n1 n2) st None
    | someNoneIfieldEvalLhsRel : forall (n1 n2:nat) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h None ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someArIfieldEvalLhsRel : forall (n1 n2:nat) (array:Array) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (ar array)) ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someTopIfieldEvalLhsRel : forall (n1 n2:nat) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob topObj)) ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someDobjIfieldEvalLhsRel : forall (n1 n2:nat) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob dobj)) ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someObjNoneIfieldEvalLhsRel : forall (n1 n3 n4:nat) (n2:FieldLocation) (lc:Location) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (lst:list (FieldLocation*Val)),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob (obj n3 n4 lst))) ->
                              LVLIST.findRel (n2,(ref null)) compFirst lst None ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someObjSomeNoneIfieldEvalLhsRel : forall (n1 n3 n4 n5:nat) (lc:Location) (n2:FieldLocation) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (lst:list (FieldLocation*Val)),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob (obj n3 n4 lst))) ->
                              LVLIST.findRel (n2,(ref null)) compFirst lst (Some n5) ->
                              LVLIST.getRel n5 lst None ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) None
    | someObjSomeSomeIfieldEvalLhsRel : forall (n1 n3 n4 n5 n6:nat) (lc:Location) (n2:FieldLocation) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (lst:list (FieldLocation*Val)) (v1:Val),
                              evalRegRel n1 (dst frms h sh inb outb) (Some (ref (lRef lc))) ->
                              HP.getRel lc h (Some (dob (obj n3 n4 lst))) ->
                              LVLIST.findRel (n2,(ref null)) compFirst lst (Some n5) ->
                              LVLIST.getRel n5 lst (Some (n6,v1)) ->
                              evalLhsRel (ifield n1 n2) (dst frms h sh inb outb) (Some v1)
    | noneSfieldEvalLhsRel : forall (n:FieldLocation) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              SVLIST.findRel (n,(ref null)) compFirst sh None ->
                              evalLhsRel (sfield n) (dst frms h sh inb outb) None
    | someNoneSfieldEvalLhsRel : forall (n:FieldLocation) (n2:nat) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                              SVLIST.findRel (n,(ref null)) compFirst sh (Some n2) ->
                              SVLIST.getRel n2 sh None ->
                              evalLhsRel (sfield n) (dst frms h sh inb outb) None
    | someSomeSfieldEvalLhsRel : forall (n:FieldLocation) (n2 n3:nat) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (v1:Val),
                              SVLIST.findRel (n,(ref null)) compFirst sh (Some n2) ->
                              SVLIST.getRel n2 sh (Some (n3,v1)) ->
                              evalLhsRel (sfield n) (dst frms h sh inb outb) (Some v1)
    | stuckEvalLhsRel : forall (l1:lhs), evalLhsRel l1 stuck None
    | haltEvalLhsRel : forall (l1:lhs), evalLhsRel l1 halt None.

  Theorem evalLhsRelEq : forall (l1:lhs) (st:DVMState) (v1:@Option Val), evalLhs l1 st = v1 <-> evalLhsRel l1 st v1.
  Proof.
    split; intro.
    destruct st; simpl in H; subst; destruct l1; simpl; try constructor; (try (destruct r; constructor)).
    remember (evalReg r (dst frms h sh inb outb)) as eregr. destruct eregr; symmetry in Heqeregr; apply evalRegRelEq in Heqeregr; assumption.
    remember (evalReg r (dst frms h sh inb outb)) as eregr. destruct eregr; symmetry in Heqeregr; try (apply evalRegRelEq in Heqeregr; apply noneFirstAccEvalLhsRel; assumption).
    destruct v. eapply somePrimFirstAccEvalLhsRel. eapply evalRegRelEq. eauto.
    destruct r1; (try (apply someNullFirstAccEvalLhsRel; apply evalRegRelEq; auto)).
    remember (HP.get l h) as getl. destruct getl; symmetry in Heqgetl; apply HP.getRelEq in Heqgetl.
      destruct t. destruct a.
        remember (evalReg r0 (dst frms h sh inb outb)) as eregr0. destruct eregr0; symmetry in Heqeregr0; apply evalRegRelEq in Heqeregr0.
          destruct v. remember (VLIST.get (PType.toNat p) l0) as get2. symmetry in Heqget2. remember (PType.toNat p) as n'. symmetry in Heqn'.
          eapply someSomeArAccEvalLhsRel. eapply evalRegRelEq. eapply Heqeregr. eapply Heqgetl. apply Heqeregr0. eapply PType.toNatRelEq. eapply Heqn'.
          eapply VLIST.getRelEq. assumption. eapply someRefSecondAccEvalLhsRel. eapply Heqeregr0.
          eapply noneSecondAccEvalLhsRel. assumption. 
          remember (evalReg r0 (dst frms h sh inb outb)) as eregr0. destruct eregr0; symmetry in Heqeregr0.
            eapply someSomeDobAccEvalLhsRel. eapply evalRegRelEq. eapply Heqeregr. eapply Heqgetl.
          eapply noneSecondAccEvalLhsRel. eapply evalRegRelEq. assumption.
          eapply someNoneAccEvalLhsRel. eapply evalRegRelEq. eapply Heqeregr. assumption.
    remember (evalReg r (dst frms h sh inb outb)) as eregr. destruct eregr; symmetry in Heqeregr; apply evalRegRelEq in Heqeregr; (try (eapply noneFirstIfieldEvalLhsRel; assumption)).
    destruct v. eapply somePrimFirstIfieldEvalLhsRel. apply Heqeregr.
    destruct r0. remember (HP.get l h) as getl. symmetry in Heqgetl. apply HP.getRelEq in Heqgetl. destruct getl.
    destruct t. eapply someArIfieldEvalLhsRel. apply Heqeregr. apply Heqgetl.
    destruct o. eapply someTopIfieldEvalLhsRel. apply Heqeregr. assumption.
    remember (LVLIST.find (f, ref null) compFirst l0) as fres. symmetry in Heqfres. apply LVLIST.findRelEq in Heqfres.
    destruct fres. remember (LVLIST.get n l0) as getl0. symmetry in Heqgetl0. apply LVLIST.getRelEq in Heqgetl0. destruct getl0.
    destruct t. eapply someObjSomeSomeIfieldEvalLhsRel. eapply Heqeregr. eapply Heqgetl. eapply Heqfres. eapply Heqgetl0.
    eapply someObjSomeNoneIfieldEvalLhsRel. eapply Heqeregr. eapply Heqgetl. eapply Heqfres. eapply Heqgetl0.
    eapply someObjNoneIfieldEvalLhsRel. eapply Heqeregr. eapply Heqgetl. eapply Heqfres.
    eapply someDobjIfieldEvalLhsRel. eapply Heqeregr. eapply Heqgetl.
    eapply someNoneIfieldEvalLhsRel. eapply Heqeregr. eapply Heqgetl.
    apply someNullFirstIfieldEvalLhsRel. assumption.
    remember (SVLIST.find (f, ref null) compFirst sh) as fres. symmetry in Heqfres. apply SVLIST.findRelEq in Heqfres.
    destruct fres. remember (SVLIST.get n sh) as getn. symmetry in Heqgetn. apply SVLIST.getRelEq in Heqgetn.
    destruct getn. destruct t. eapply someSomeSfieldEvalLhsRel. eapply Heqfres. eapply Heqgetn.
    eapply someNoneSfieldEvalLhsRel. eapply Heqfres. assumption.
    eapply noneSfieldEvalLhsRel. assumption.
    (* If part done *)
    inversion H; simpl.
      apply evalRegRelEq in H0; rewrite H0; reflexivity.
      apply evalRegRelEq in H0; rewrite H0; destruct st; reflexivity.
      apply evalRegRelEq in H0; rewrite H0; destruct st; reflexivity.
      apply evalRegRelEq in H0; rewrite H0; destruct st; reflexivity.
      apply evalRegRelEq in H0; rewrite H0; destruct st; try reflexivity. destruct (evalReg n (dst frms h sh inb outb)); destruct v; auto; destruct r; auto. destruct (HP.get l h); auto. destruct t; auto. destruct a; auto.
      apply evalRegRelEq in H0; rewrite H0; destruct st; try reflexivity. destruct (evalReg n (dst frms h sh inb outb)); destruct v; auto; destruct r0; auto. destruct (HP.get l h); auto. destruct t; auto. destruct a; auto.
      apply evalRegRelEq in H0; rewrite H0. eapply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0. eapply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0. eapply HP.getRelEq in H1. rewrite H1. apply evalRegRelEq in H2. rewrite H2. apply PType.toNatRelEq in H3. rewrite H3. apply VLIST.getRelEq. assumption.
      destruct st; auto; apply evalRegRelEq in H0; rewrite H0; auto.
      destruct st; auto; apply evalRegRelEq in H0; rewrite H0; auto.
      destruct st; auto; apply evalRegRelEq in H0; rewrite H0; auto.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1.
      apply LVLIST.findRelEq in H2. rewrite H2. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. apply LVLIST.findRelEq in H2. rewrite H2. apply LVLIST.getRelEq in H3. rewrite H3. reflexivity.
      apply evalRegRelEq in H0; rewrite H0; auto. apply HP.getRelEq in H1. rewrite H1. apply LVLIST.findRelEq in H2. rewrite H2. apply LVLIST.getRelEq in H3. rewrite H3. reflexivity.
      apply SVLIST.findRelEq in H0. rewrite H0. reflexivity.
      apply SVLIST.findRelEq in H0. rewrite H0. apply SVLIST.getRelEq in H1. rewrite H1. reflexivity.
      apply SVLIST.findRelEq in H0. rewrite H0. apply SVLIST.getRelEq in H1. rewrite H1. reflexivity.
      destruct l1; simpl; auto. apply evalRegRelEq. constructor.
      destruct l1; simpl; auto. apply evalRegRelEq. constructor.
  Qed.
(* ShortCuts
      try (destruct st; simpl; reflexivity); try (apply HP.getRelEq in H1; rewrite H1; simpl; auto); try (destruct l1; simpl; reflexivity).
      destruct st; try reflexivity. destruct (evalReg n (dst frms h sh inb outb)); destruct v; simpl; try reflexivity. destruct r; auto. destruct (HP.get l h); auto. destruct t; auto. destruct a; auto.
      destruct st; try reflexivity. destruct (evalReg n (dst frms h sh inb outb)); destruct v; simpl; try reflexivity. destruct r0; auto. destruct (HP.get l h); auto. destruct t; auto. destruct a; auto.
      apply evalRegRelEq in H2. rewrite H2. apply PType.toNatRelEq in H3. rewrite H3. apply VLIST.getRelEq. assumption.
*)

(* Bug Alert ! pattern matching bug *)

(**

** evalRhs : Evaluates rhs expressions

*)

  Definition evalRhs (exp:rhs) (st:DVMState) : @Option Val :=
    match exp with
    | (l lhs1) => (evalLhs lhs1 st)
    | (cs cnst) => match cnst with
      | cnat n => Some (prim (int n))
      | ctrue => Some (prim (boolean 1))
      | cfalse => Some (prim (boolean 0))
      | cnull => Some (ref null)
      end
    end.

  Inductive evalRhsRel : rhs -> DVMState -> @Option Val -> Prop :=
    | lhsEvalRhsRel : forall (l1:lhs) (st:DVMState) (v:@Option Val), evalLhsRel l1 st v -> evalRhsRel (l l1) st v
    | cnatEvalRhsRel : forall (n:nat) (st:DVMState), evalRhsRel (cs (cnat n)) st (Some (prim (int n)))
    | ctrueEvalRhsRel : forall (st:DVMState), evalRhsRel (cs ctrue) st (Some (prim (boolean 1)))
    | cfalseEvalRhsRel : forall (st:DVMState), evalRhsRel (cs cfalse) st (Some (prim (boolean 0)))
    | cnullEvalRhsRel : forall (st:DVMState), evalRhsRel (cs cnull) st (Some (ref null)).

  Theorem evalRhsRelEq : forall (r1:rhs) (st:DVMState) (v1:@Option Val), evalRhs r1 st = v1 <-> evalRhsRel r1 st v1.
  Proof.
    split; intro.
    destruct r1. simpl in H. apply evalLhsRelEq in H. constructor. assumption.
    destruct c; simpl in H; rewrite <- H; constructor.
    inversion H; simpl; auto. apply evalLhsRelEq. assumption.
  Qed.

End EVAL.