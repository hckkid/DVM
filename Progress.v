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

Theorem mkChangesHaltsOnHalt : forall chs, mkChanges halt chs = Some halt.
Proof.
  induction chs. reflexivity. simpl. assumption. Qed.

Theorem mkChangesStuckOnStuck : forall chs, mkChanges stuck chs = Some stuck.
Proof.
  induction chs. reflexivity. simpl. assumption. Qed.

Inductive isUpdateFrameVal : deltaState -> Prop :=
  upValProp : forall n v, isUpdateFrameVal (updateFrame (upVals n v)).

Theorem mkChangesProgressOnUpdateFrameValPairs : forall l, forAllList l isUpdateFrameVal ->
  forall rvs m pc frms h sh inb outb,
  exists rvs',
  mkChanges (dst (frm rvs m pc :: frms) h sh inb outb) l = Some (dst (frm rvs' m pc :: frms) h sh inb outb).
Proof.
  intros l H.
  induction l.
    eexists; simpl; reflexivity.
    simpl. inversion H. destruct a; try inversion H2.
    intros. destruct (VLIST.find (n, v) compFirst rvs);
    eapply IHl; assumption.
  Qed. 

Theorem evalHpInstHeapEq : forall loc1 h,EVAL.HP.get loc1 h = INSTRUCTION.HEAP.get loc1 h.
Proof.
  intros.
  unfold EVAL.HP.get. unfold INSTRUCTION.HEAP.get. reflexivity.
Qed.

Theorem progressNop : forall (st:DVMState) (p:Program), consistentNop st p -> 
  (exists st',INSTRUCTION.stepWith nop st p = Some st' /\ ~(st' = stuck)).
Proof.
  destruct st.
  intros. inversion H. unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst.
  unfold INSTRUCTION.evalNop. rewrite H6. rewrite H7. simpl. eexists. split. reflexivity.
  intro Contra; inversion Contra.
  intros. inversion H. intros. eexists. split. reflexivity. intro Contra; inversion Contra.
Qed.

Theorem progressRet : forall (st:DVMState) (p:Program), consistentRet st p -> 
  (exists st',INSTRUCTION.stepWith ret st p = Some st' /\ ~(st' = stuck)).
Proof.
  destruct st; intros. inversion H. unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst.
  unfold INSTRUCTION.evalRet. rewrite H6. rewrite H7.
  destruct (EVAL.evalReg 201 (dst (f :: frm vals ml pc :: frms0) h sh inb outb)).
    remember (upVals 201 v) as trv.
    simpl. destruct trv.
    destruct (VLIST.find (n, v0) compFirst vals). simpl. eexists.
    split. reflexivity. intro Contra. inversion Contra.
    eexists. split. reflexivity. intro Contra. inversion Contra.
    inversion Heqtrv.
    eexists. split. reflexivity. intro Contra. inversion Contra.
    inversion H. eexists. split. reflexivity. intro Contra. inversion Contra.
Qed.  

Theorem progressRetTo : forall (st:DVMState) (p:Program) r, consistentRet st p -> 
  (exists st',INSTRUCTION.stepWith (retTo r) st p = Some st' /\ ~(st' = stuck)).
Proof.
  destruct st; intros. inversion H. unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst.
  unfold INSTRUCTION.evalRetTo. rewrite H6. rewrite H7.
  destruct (EVAL.evalReg 201 (dst (f :: frm vals ml pc :: frms0) h sh inb outb)).
    remember (upVals r v) as trv.
    simpl. destruct trv.
    destruct (VLIST.find (n, v0) compFirst vals). simpl. eexists.
    split. reflexivity. intro Contra. inversion Contra.
    eexists. split. reflexivity. intro Contra. inversion Contra.
    inversion Heqtrv.
    eexists. split. reflexivity. intro Contra. inversion Contra.
    inversion H. eexists. split. reflexivity. intro Contra. inversion Contra.
Qed.

Theorem progressInvokes : forall (st:DVMState) (p:Program) l m, consistentInvokes st p l m ->
(exists st' : DVMState, INSTRUCTION.stepWith (invokes l m) st p = Some st' /\ st' <> stuck).
Proof.
  intros. inversion H;
  unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst; unfold INSTRUCTION.evalInvokes.
  rewrite H0. assert (filter (map l (fun x : rhs => EVAL.evalRhs x (dst frms h sh inb outb))) isNone = []).
  eapply forAllListFilter; try apply H1. intros. eapply progressRhs. apply H6.
  rewrite H6. remember (numberList 101
                (map (fastRev l)
                   (fun x : rhs =>
                    match EVAL.evalRhs x (dst frms h sh inb outb) with
                    | Some v1 => v1
                    | None => ref null
                    end))) as tlist.
  remember (fastRev
          (map tlist
             (fun x : nat * Val =>
              let (nx, vx) := x in updateFrame (upVals nx vx)))) as revMacro.
  assert (forAllList revMacro isUpdateFrameVal). rewrite HeqrevMacro. rewrite <- rev_pres.
  assert (forall lst',forAllList
  (map lst'
     (fun x : nat * Val => let (nx, vx) := x in updateFrame (upVals nx vx)))
  isUpdateFrameVal).
  induction lst'; simpl; econstructor. destruct a; simpl; econstructor. assumption.
  apply H7. simpl. eapply mkChangesProgressOnUpdateFrameValPairs in H7. inversion H7.
  eexists. split. apply H8. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressInvokei : forall (st:DVMState) (p:Program) r l m, consistentInvokei st p l m r ->
(exists st' : DVMState, INSTRUCTION.stepWith (invokei r l m) st p = Some st' /\ st' <> stuck).
Proof.
  intros. inversion H;
  unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst; unfold INSTRUCTION.evalInvokei.
  rewrite H0. assert (filter (map l (fun x : rhs => EVAL.evalRhs x (dst frms h sh inb outb))) isNone = []).
  eapply forAllListFilter; try apply H1. intros. eapply progressRhs. apply H8.
  rewrite H8. remember (numberList 101
                (map (fastRev l)
                   (fun x : rhs =>
                    match EVAL.evalRhs x (dst frms h sh inb outb) with
                    | Some v1 => v1
                    | None => ref null
                    end))) as tlist.
  remember (fastRev
          (map tlist
             (fun x : nat * Val =>
              let (nx, vx) := x in updateFrame (upVals nx vx)))) as revMacro.
  assert (forAllList revMacro isUpdateFrameVal). rewrite HeqrevMacro. rewrite <- rev_pres.
  assert (forall lst',forAllList
  (map lst'
     (fun x : nat * Val => let (nx, vx) := x in updateFrame (upVals nx vx)))
  isUpdateFrameVal).
  induction lst'; intros; simpl; econstructor. destruct a; simpl; econstructor. assumption.
  apply H9. simpl.
  apply progressReg in H2. destruct (EVAL.evalReg r (dst frms h sh inb outb)).
  assert (forAllList ((updateFrame (upVals 0 v))::revMacro) isUpdateFrameVal).
  constructor; try assumption. constructor.
  eapply mkChangesProgressOnUpdateFrameValPairs in H10.
  inversion H10. remember (updateFrame (upVals 0 v) :: revMacro) as tup. simpl. rewrite H11.
  eexists. split.
  reflexivity. intro Contra; inversion Contra.
  inversion H2.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressGoto : forall (st:DVMState) (p:Program) p0, consistentGoto st p p0 ->
  (exists st' : DVMState, INSTRUCTION.stepWith (goto p0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalGoto.
  simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
  eexists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressBranch : forall (st:DVMState) (p:Program) b p0 r r0, consistentBranch st p r r0 b p0 -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (branch r b r0 p0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalBranch.
  apply EVAL.evalRhsRelEq in H0. rewrite H0.
  apply EVAL.evalRhsRelEq in H1. rewrite H1.
  destruct b.
    destruct (PType.comp p2 p3 + PType.comp p3 p2)%nat.
      simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
      inversion H2. simpl. rewrite H16. rewrite H17. simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
    destruct (PType.comp p3 p2).
      inversion H2. simpl. rewrite H16. rewrite H17. simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
      simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
    destruct (PType.comp p2 p3).
      inversion H2. simpl. rewrite H16. rewrite H17. simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
      simpl. eexists. split. reflexivity. intro Contra. inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressMove : forall (st:DVMState) (p:Program) r r0, consistentMove st p r r0 -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (move r r0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith.
  unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalMove.
  apply progressRhs in H0. destruct (EVAL.evalRhs r0 (dst frms h sh inb outb)).
  inversion H1. simpl. rewrite H12. rewrite H13. simpl.
  eexists. split. reflexivity.
  intro Contra; inversion Contra. inversion H0.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressUpdate : forall (st:DVMState) (p:Program) r r0, consistentUpdate st p r r0 -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (update r r0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith;
  unfold INSTRUCTION.evalInst; unfold INSTRUCTION.evalUpdate.
  apply progressRhs in H0.
    destruct (EVAL.evalRhs r0 (dst frms h sh inb outb)).
      apply EVAL.evalRegRelEq in H1. rewrite H1. apply EVAL.evalRegRelEq in H2. rewrite H2.
      apply EVAL.HP.getRelEq in H3.
      rewrite evalHpInstHeapEq in H3. rewrite H3. apply PType.toNatRelEq in H4. rewrite H4.
        unfold lt in H5. apply Sn_Sm_le_n_m in H5. apply isleNumProp in H5. rewrite H5.
      inversion H6. simpl. rewrite H17. rewrite H18. simpl.
      eexists. split. reflexivity. intro Contra; inversion Contra.
      inversion H0.
  apply progressRhs in H0.
    destruct (EVAL.evalRhs r0 (dst frms h sh inb outb)).
      apply EVAL.evalRegRelEq in H1. rewrite H1.
      apply EVAL.HP.getRelEq in H2. rewrite evalHpInstHeapEq in H2. rewrite H2.
      apply INSTRUCTION.FLIST.findRelEq in H3. rewrite H3. simpl.
      inversion H4. rewrite H15. rewrite H16. simpl. eexists; split. reflexivity. intro Contra; inversion Contra.
      inversion H0.
  apply progressRhs in H0.
    destruct (EVAL.evalRhs r0 (dst frms h sh inb outb)).
      apply INSTRUCTION.FLIST.findRelEq in H1. rewrite H1. simpl.
      inversion H2. rewrite H13. rewrite H14. simpl. eexists; split. reflexivity. intro Contra; inversion Contra.
      inversion H0.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressUnary : forall (st:DVMState) (p:Program) r r0 u, consistentUnary st p r r0 u -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (unary r u r0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H. unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst.
  unfold INSTRUCTION.evalUnary. apply progressRhs in H0.
  destruct (EVAL.evalRhs r0 (dst frms h sh inb outb)).
  destruct v; try destruct (isle_num 1 (PType.toNat p1));
  try destruct r2;
    repeat (eapply progressMove;
      constructor; try assumption; try constructor).
  inversion H0.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressBinary : forall (st:DVMState) (p:Program) r r0 r1 b, consistentBinaryArith st p r r0 r1 b -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (binaryArith r r0 b r1) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith.
  unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalBinaryArith.
  apply EVAL.evalRhsRelEq in H0. rewrite H0.
  apply EVAL.evalRhsRelEq in H1. rewrite H1.
  destruct b; repeat (eapply progressMove; constructor; try assumption; constructor).
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressNew : forall (st:DVMState) (p:Program) r c, consistentNew st p r c -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (new r c) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith.
  unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalNew.
  rewrite H0. simpl. inversion H1. rewrite H12. rewrite H13.
  simpl. eexists. split. reflexivity. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressNewArray : forall (st:DVMState) (p:Program) r t r0, consistentNewArray st p r t r0 -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (newarr r t r0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith.
  unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalNewArray.
  apply EVAL.evalRhsRelEq in H0. rewrite H0.
  rewrite <- PType.toNatRelEq in H1. rewrite H1.
  rewrite H2. inversion H3. simpl. rewrite H15. rewrite H16.
  simpl. eexists. split. reflexivity. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressCast : forall (st:DVMState) (p:Program) r t r0, consistentCast st p r t r0 -> 
  (exists st' : DVMState, INSTRUCTION.stepWith (cast r t r0) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith.
  unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalCast.
  apply EVAL.evalRhsRelEq in H0. rewrite H0. rewrite H1.
  unfold TYPE.cast in H1.
  destruct (TYPE.HEAP.get loc1 h); try inversion H1.
  destruct t0; try inversion H1. destruct o; try inversion H1.
  destruct t; try inversion H1. destruct r2; try inversion H1.
  destruct (TYPE.isSub p c1 c0); try inversion H1. simpl.
  subst. inversion H2. rewrite H14. rewrite H15. simpl.
  eexists. split. reflexivity. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressRead : forall (st:DVMState) (p:Program) r, consistentRead st p r ->
  (exists st' : DVMState, INSTRUCTION.stepWith (read r) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalRead.
  simpl. apply INSTRUCTION.NLIST.getRelEq in H0. rewrite H0.
  inversion H1. rewrite H11. rewrite H12. simpl.
  eexists. split. reflexivity. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progressWrite : forall (st:DVMState) (p:Program) r, consistentWrite st p r ->
  (exists st' : DVMState, INSTRUCTION.stepWith (print r) st p = Some st' /\ st' <> stuck).
Proof.
  intros; inversion H; unfold INSTRUCTION.stepWith. unfold INSTRUCTION.evalInst. unfold INSTRUCTION.evalWrite.
  simpl. destruct outb. apply EVAL.evalRhsRelEq in H0. rewrite H0.
  inversion H1. rewrite H11. rewrite H12. simpl.
  eexists. split. reflexivity. intro Contra; inversion Contra.
  exists halt. split. apply mkChangesHaltsOnHalt. intro Contra; inversion Contra.
Qed.

Theorem progress : forall (st:DVMState) (p:Program) (i:Instruction), consistentInst i st p -> 
  (exists st',INSTRUCTION.stepWith i st p = Some st' /\ ~(st' = stuck)).
Proof.
    intros st p.
    generalize dependent p.
    destruct i; intros; inversion H.
    (** nop *)
      apply progressNop. assumption.
    (** ret *)
      apply progressRet. assumption.
    (** retTo *)
      apply progressRetTo. assumption.
    (** invokes *)
      apply progressInvokes. assumption.
    (** invokei *)
      apply progressInvokei. assumption.
    (** goto *)
      apply progressGoto. assumption.
    (** branch *)
      apply progressBranch. assumption.
    (** move *)
      apply progressMove. assumption.
    (** update *)
      apply progressUpdate. assumption.
    (** unary *)
      apply progressUnary. replace u with uop. apply H4. destruct u. destruct uop. reflexivity.
    (** binary *)
      apply progressBinary. assumption.
    (** new *)
      apply progressNew. assumption.
    (** newarr *)
      apply progressNewArray. assumption.
    (** cast *)
      apply progressCast. assumption.
    (** Read *)
      apply progressRead. assumption.
    (** W *)
      apply progressWrite. assumption.
Qed.