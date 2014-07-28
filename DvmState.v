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

  Definition changeFrame (currf:Frame) (fd:frameDiff) : Frame :=
    match currf,fd with
    | (frm vals ml pc),(upPC pc2) => frm vals ml pc2
    | (frm vals ml pc),(upVals n v1) => match (VLIST.find (n,v1) compFirst vals) with
      | Some n' => frm (VLIST.set n' (n,v1) vals) ml pc
      | None => frm (VLIST.prep (n,v1) vals) ml pc
      end
    end.

  Inductive changeFrameRel : Frame -> frameDiff -> Frame -> Prop :=
    | upPCRel : forall (vals:list (nat*Val)) (ml:MethodLocation) (pc pc2:ProgramCounter), changeFrameRel (frm vals ml pc) (upPC pc2) (frm vals ml pc2)
    | upValsRel1 : forall (vals1 vals2:list (nat*Val)) (n n1:nat) (v1:Val) (ml:MethodLocation) (pc:ProgramCounter), VLIST.findRel (n,v1) compFirst vals1 (Some n1) -> VLIST.setRel n1 (n,v1) vals1 vals2 -> changeFrameRel (frm vals1 ml pc) (upVals n v1) (frm vals2 ml pc)
    | upValsRel2 : forall (vals vals2:list (nat*Val)) (n:nat) (v1:Val) (ml:MethodLocation) (pc:ProgramCounter), VLIST.findRel (n,v1) compFirst vals None -> VLIST.prepRel (n,v1) vals vals2 -> changeFrameRel (frm vals ml pc) (upVals n v1) (frm vals2 ml pc).

  Theorem changeFrameRelEq : forall (f1 f2:Frame) (fd:frameDiff), changeFrame f1 fd = f2 <-> changeFrameRel f1 fd f2.
  Proof.
    destruct f1.
    destruct fd; split; intros.
      simpl in H.
      remember (VLIST.find (n, v) compFirst vals) as fres.
      destruct fres; rewrite <- H. 
        eapply upValsRel1. eapply VLIST.findRelEq. symmetry. eapply Heqfres. apply VLIST.setRelEq. reflexivity.
        eapply upValsRel2. eapply VLIST.findRelEq. symmetry. eapply Heqfres. apply VLIST.prepRelEq. reflexivity.
      inversion H; simpl; apply VLIST.findRelEq in H6; rewrite H6. 
        apply VLIST.setRelEq in H7. rewrite H7. reflexivity.
        apply VLIST.prepRelEq in H7. rewrite H7. reflexivity.
      simpl in H. rewrite <- H. econstructor.
      inversion H. simpl. reflexivity.
  Qed.

  Declare Module ABLIST : ListType with Definition t1 := arrOrObj.
  Declare Module NLIST : ListType with Definition t1 := nat.

  Definition mkChange (cst:state) (ch:change) : @Option state :=
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

  Inductive mkChangeRel : state -> change -> @Option state -> Prop :=
    | createFrameRel : forall (frms: list Frame) (f:Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), mkChangeRel (dst frms h sh inb outb) (createFrame f) (Some (dst (cons f frms) h sh inb outb))
    | updateFrameRel : forall (frms: list Frame) (f1 f2:Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer) (fd:frameDiff),
                         (changeFrameRel f1 fd f2) ->
                         mkChangeRel (dst (cons f1 frms) h sh inb outb) (updateFrame fd) (Some (dst (cons f2 frms) h sh inb outb))
    | deleteFrameRel : forall (frms: list Frame) (f1:Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer),
                         mkChangeRel (dst (cons f1 frms) h sh inb outb) deleteFrame (Some (dst frms h sh inb outb))
    | upHeapRel : forall (frms: list Frame) (lst:list (nat*arrOrObj)) (h h':Heap) (sh:SHeap) (inb outb:Buffer),
                         ABLIST.setManyRel lst h h' ->
                         mkChangeRel (dst frms h sh inb outb) (upHeap lst) (Some (dst frms h' sh inb outb))
    | upSHeapRel : forall (frms: list Frame) (h:Heap) (sh sh':SHeap) (inb outb:Buffer),
                         mkChangeRel (dst frms h sh inb outb) (upSHeap sh') (Some (dst frms h sh' inb outb))
    | upInbRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (curs:Cursor) (clst:list (nat*nat)) (lst lst':list nat) (outb:Buffer),
                         NLIST.setManyRel clst lst lst' ->
                         mkChangeRel (dst frms h sh (curs,lst) outb) (upInb clst) (Some (dst frms h sh (curs,lst') outb))
    | upIncRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (curs1 curs2:Cursor) (lst:list nat) (outb:Buffer),
                         mkChangeRel (dst frms h sh (curs1,lst) outb) (upInc curs2) (Some (dst frms h sh (curs2,lst) outb))
    | upOutbRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (curs:Cursor) (clst:list (nat*nat)) (lst lst':list nat) (inb:Buffer),
                         NLIST.setManyRel clst lst lst' ->
                         mkChangeRel (dst frms h sh inb (curs,lst)) (upOutb clst) (Some (dst frms h sh inb (curs,lst')))
    | upOutcRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (curs1 curs2:Cursor) (lst:list nat) (inb:Buffer),
                         mkChangeRel (dst frms h sh inb (curs1,lst)) (upOutc curs2) (Some (dst frms h sh inb (curs2,lst)))
    | mkStuckRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), mkChangeRel (dst frms h sh inb outb) mkStuck (Some stuck)
    | mkHaltRel : forall (frms: list Frame) (h:Heap) (sh:SHeap) (inb outb:Buffer), mkChangeRel (dst frms h sh inb outb) mkHalt (Some halt)
    | updateFrameRel2 : forall (h:Heap) (sh:SHeap) (inb outb:Buffer) (fd:frameDiff),
                         mkChangeRel (dst nil h sh inb outb) (updateFrame fd) None
    | deleteFrameRel2 : forall (h:Heap) (sh:SHeap) (inb outb:Buffer),
                         mkChangeRel (dst nil h sh inb outb) deleteFrame None
    | stuckRel : forall (ch:change), mkChangeRel stuck ch (Some stuck)
    | haltRel : forall (ch:change), mkChangeRel halt ch (Some halt).

  Theorem mkChangeRelEq : forall (st:state) (ch:change) (fst:@Option state), mkChange st ch = fst <-> mkChangeRel st ch fst.
  Proof.
    intros st ch.
    generalize dependent st.
    destruct ch; split; intro;
      try (destruct st; simpl in H; subst; econstructor);
      try (inversion H; simpl; reflexivity).
      destruct st; try destruct frms; try simpl in H; try subst; try econstructor. apply changeFrameRelEq. reflexivity.
      inversion H; simpl; try reflexivity. apply changeFrameRelEq in H2. subst. reflexivity.
      destruct st; try destruct frms; simpl in H; subst; econstructor.
      apply ABLIST.setManyRelEq. reflexivity.
      inversion H; simpl; try reflexivity. apply ABLIST.setManyRelEq in H2. rewrite H2. reflexivity.
      destruct st; try destruct inb; simpl in H; subst; try econstructor. apply NLIST.setManyRelEq. reflexivity.
      inversion H; simpl; try reflexivity; try apply NLIST.setManyRelEq in H2; subst; try reflexivity.
      destruct st; try destruct outb; simpl in H; subst; try econstructor. apply NLIST.setManyRelEq. reflexivity.
      inversion H; simpl; try reflexivity; try apply NLIST.setManyRelEq in H2; subst; try reflexivity.
      destruct st; try destruct inb; simpl in H; subst; try econstructor.
      destruct st; try destruct outb; simpl in H; subst; try econstructor.
  Qed.

  Fixpoint mkChanges (cst:state) (chs:list change) : @Option state :=
    match chs with
    | nil => Some cst
    | (cons ch1 chrem) => match (mkChange cst ch1) with
      | (Some cst') => (mkChanges cst' chrem)
      | None => None
      end
    end.

  Inductive mkChangesRel : state -> list change -> (@Option state) -> Prop :=
    | nilMkChangesRel : forall (s:state), mkChangesRel s nil (Some s)
    | someMkChangesRel : forall (s1 s2:state) (s3:@Option state) (ch1:change) (chrem:list change),
                         mkChangeRel s1 ch1 (Some s2) ->
                         mkChangesRel s2 chrem s3 ->
                         mkChangesRel s1 (cons ch1 chrem) s3
    | noneMkChangesRel : forall (s1:state) (ch1:change) (chrem:list change),
                         mkChangeRel s1 ch1 None ->
                         mkChangesRel s1 (cons ch1 chrem) None.

  Theorem mkChangesRelEq : forall (st1:state) (st2:@Option state) (chs:list change), mkChanges st1 chs = st2 <-> mkChangesRel st1 chs st2.
  Proof.
    intros.
    generalize dependent st1.
    generalize dependent st2.
    induction chs; split; intro.
      simpl in H; subst; econstructor.
      inversion H; simpl; reflexivity.
      simpl in H. remember (mkChange st1 a) as st'. destruct st'.
        econstructor. eapply mkChangeRelEq. rewrite <- Heqst'. eauto. apply IHchs. assumption.
        subst. symmetry in Heqst'. apply mkChangeRelEq in Heqst'. constructor. assumption.
      inversion H; simpl; subst. apply mkChangeRelEq in H3; subst. rewrite H3. apply IHchs. assumption.
      apply mkChangeRelEq in H4; subst. rewrite H4. reflexivity.
  Qed.

End ChangeState.