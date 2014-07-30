Add LoadPath "D:\DVM".
Require Export Consistency.

Theorem pregress : forall (st:DVMState) (p:Program) (i:Instruction), consistentInst i st p -> 
  (exists st',INSTRUCTION.stepWith i st p = Some st' /\ ~(st' = stuck)).
Proof.
  destruct st.
    intros p i.
    generalize dependent p.
    destruct i; intros; inversion H.
(** Case 1 : Nop *)
      inversion H0; simpl; eapply ex_intro. split. unfold INSTRUCTION.stepWith.
        unfold INSTRUCTION.evalInst. simpl. rewrite H9. rewrite H10. reflexivity.
        intro. inversion H11.
(** Case 2 : Ret *)