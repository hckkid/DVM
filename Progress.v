Add LoadPath "D:\DVM".
Require Export Consistency.

(**

* Overview

Here we will prove progress property for CoqDVM, which can be described as

forall (st:DVMState) (p:Program) (i:Instruction), consistentInst i st p -> 
  (exists st',INSTRUCTION.stepWith i st p = Some st' /\ ~(st' = stuck))

*)

Theorem progressReg : forall (x:Register) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), consistentEvalReg x (dst frms h sh inb outb) ->
  isNone (EVAL.evalReg x (dst frms h sh inb outb)) = false.
Proof.
  intros. inversion H. unfold EVAL.evalReg. destruct x; apply EVAL.RLIST.findRelEq in H2; rewrite H2; simpl.
  assert (exists v,EVAL.RLIST.get n' vals = Some v).
    eapply EVAL.RLIST.get_find. apply H2.
    inversion H7. rewrite H8. destruct x. simpl. reflexivity.
    apply EVAL.RLIST.get_find in H2. inversion H2. rewrite H7. destruct x0. simpl. reflexivity.
  Qed.

Theorem progressLhs : forall (x:lhs) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), consistentEvalLhs x (dst frms h sh inb outb) ->
  isNone (EVAL.evalLhs x (dst frms h sh inb outb)) = false.
Proof.
  intros. inversion H.
    simpl. apply progressReg. assumption.
    simpl. apply EVAL.evalRegRelEq in H5. apply EVAL.evalRegRelEq in H8.
    rewrite H5. apply EVAL.HP.getRelEq in H7. rewrite H7. rewrite H8. rewrite <- H9 in H11. eapply EVAL.VLIST.get_avail in H11.
    apply PType.toNatRelEq in H10. rewrite H10. inversion H11. rewrite H12. reflexivity.
    assert (exists v', EVAL.evalLhs (ifield n n2) (dst frms h sh inb outb) = Some v').
      remember (EVAL.evalLhs (ifield n n2) (dst frms h sh inb outb)) as tmp.
        destruct vl. exists v. rewrite Heqtmp.
        eapply EVAL.evalLhsRelEq. econstructor; try eassumption.
    inversion H10. rewrite H11. simpl. reflexivity.
    assert (exists v', EVAL.evalLhs (sfield n) (dst frms h sh inb outb) = Some v').
      destruct vl. exists v. apply EVAL.evalLhsRelEq. econstructor.
        apply H3. apply H7. inversion H8. rewrite H9.
    reflexivity.
  Qed.

Theorem progressRhs : forall (x:rhs) (frms:list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), consistentEvalRhs x (dst frms h sh inb outb) ->
  isNone (EVAL.evalRhs x (dst frms h sh inb outb)) = false.
Proof.
  intros. inversion H. simpl. apply progressLhs. assumption.
  simpl. destruct cns; reflexivity.
  Qed.

Theorem progress : forall (st:DVMState) (p:Program) (i:Instruction), consistentInst i st p -> 
  (exists st',INSTRUCTION.stepWith i st p = Some st' /\ ~(st' = stuck)).
Proof.
  destruct st.
    intros p i.
    generalize dependent p.
    destruct i; intros; inversion H.
    (** nop *)
      inversion H0; simpl; eapply ex_intro. split. unfold INSTRUCTION.stepWith.
        unfold INSTRUCTION.evalInst. simpl. rewrite H9. rewrite H10. reflexivity.
        intro. inversion H11.
    (** ret *)
      inversion H0; simpl. unfold INSTRUCTION.stepWith.
        unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalRet. rewrite H9. rewrite H10.
        destruct (EVAL.evalReg 201 (dst (f :: frm vals ml pc :: frms0) h sh inb outb)); simpl.
          destruct (ChangeState.VLIST.find (201, v) compFirst vals). simpl.
          exists (dst (frm (ChangeState.VLIST.set n (201, v) vals) ml pc' :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H11.
          exists (dst (ChangeState.changeFrame (frm (ChangeState.VLIST.prep (201, v) vals) ml pc) (upPC pc') :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H11.
          exists (dst (frm vals ml pc' :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H11.
    (** retTo *)
      inversion H1; simpl. unfold INSTRUCTION.stepWith.
        unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalRetTo. rewrite H10. rewrite H11.
        destruct (EVAL.evalReg 201 (dst (f :: frm vals ml pc :: frms0) h sh inb outb)); simpl.
          destruct (ChangeState.VLIST.find (201, v) compFirst vals). simpl.
          exists (dst (ChangeState.changeFrame
                      match ChangeState.VLIST.find (r, v) compFirst vals with
                      | Some n' => frm (ChangeState.VLIST.set n' (r, v) vals) ml pc
                      | None => frm (ChangeState.VLIST.prep (r, v) vals) ml pc
                      end (upPC pc') :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H12.
          exists (dst (ChangeState.changeFrame
                      match ChangeState.VLIST.find (r, v) compFirst vals with
                      | Some n' => frm (ChangeState.VLIST.set n' (r, v) vals) ml pc
                      | None => frm (ChangeState.VLIST.prep (r, v) vals) ml pc
                      end (upPC pc') :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H12.
          exists (dst (frm vals ml pc' :: frms0) h sh inb outb).
          split. reflexivity. intro. inversion H12.
    (** invokes *)
      inversion H4. unfold INSTRUCTION.stepWith.
        unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalInvokes.
        assert ((filter (map l (fun x : rhs => EVAL.evalRhs x (dst frms h sh inb outb))) isNone) = []).
        eapply forAllListFilter.
        assert (forall x : rhs, (fun y:rhs => consistentEvalRhs y (dst frms h sh inb outb)) x -> isNone (EVAL.evalRhs x (dst frms h sh inb outb)) = false).
          intros. apply progressRhs; try eassumption. eassumption. assumption.
        rewrite H15. rewrite H13. simpl.
        (** Resolve Here *)
              destruct (fastRev
       (List.map
          (fun x : nat * Val =>
           let (nx, vx) := x in updateFrame (upVals nx vx))
          (numberList 101
             (List.map
                (fun x : rhs =>
                 match EVAL.evalRhs x (dst frms h sh inb outb) with
                 | Some v1 => v1
                 | None => ref null
                 end) (fastRev l))))). eexists. split. reflexivity.
          intro Contra. inversion Contra.
          simpl. unfold fastRev. simpl.