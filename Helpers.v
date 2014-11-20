(**

Helpers provide few key definitions general for development purpose in Coq.

* Option

*)

Require Export List.
Export ListNotations.

Inductive Option {A:Type} : Type :=
  | Some : A -> Option
  | None : Option.

(** 

* Arithmetic Definitions

In this section following arithmetic definitions are made:
- areEqualNum : returns bool result of equality on numbers
- areEqualBool : returns bool result of equality on bools
- isle_num : n1 < n2 with bool result
- div : n1 / n2 , integer division
- mod : modulo operator

*)

Fixpoint areEqualNum (n1:nat) (n2:nat) : bool :=
  match n1 with
  | O => match n2 with
    | O => true
    | _ => false
    end
  | (S n1') => match n2 with
    | O => false
    | (S n2') => (areEqualNum n1' n2')
    end
  end.

Fixpoint areEqualBool (b1 b2:bool) : bool :=
  match b1 , b2 with
  | true,true => true
  | false,false => true
  | _,_ => false
  end.

Fixpoint isle_num (m n:nat) : bool :=
  match m with
  | O => true
  | (S m') => match n with
    | O => false
    | (S n') => (isle_num m' n')
    end
  end.

Fixpoint div (m n:nat) {struct m} : nat :=
  match m with
  | O => O
  | (S m') => match (areEqualNum n (m - (mult (div m' n) n))) with
    | true => S (div m' n)
    | false => (div m' n)
    end
  end.

Definition mod (m n:nat) : nat := m - (mult (div m n) n).

(**

* List Operations

Here following generic list operations are covered:
- fold : Similar to statndard accumulator function
- map : Applies a function to all elements of list
- filter : Filters content of list based upon certain check
- numberList : numbers elements of given list, hence generating list (nat*X) for list X input
- fastRev : linear order reverse on list, makes use of temporary list
- forAllList : relation that holds if input relation holds for each element of list

*)

Fixpoint fold {X Y:Type} (l1:list X) (f:X->Y->Y) (def:Y) : Y :=
  match l1 with
  | nil => def
  | (cons x lrem) => (f x (fold lrem f def))
  end.

Inductive foldRel {X Y:Type} : list X -> (X->Y->Y) -> Y -> Y -> Prop :=
  | nilFoldRel : forall (f:X->Y->Y) (def:Y), (foldRel nil f def def)
  | someFoldRel : forall (x:X) (xrem:list X) (f:X->Y->Y) (def:Y) (res:Y), foldRel xrem f def res ->
                 foldRel (cons x xrem) f def (f x res).

Theorem foldRelEq : forall (X Y:Type) (l1:list X) (f:X->Y->Y) (def:Y) (res:Y), fold l1 f def = res <-> foldRel l1 f def res.
Proof.
  induction l1; split; intro.
    simpl in H. rewrite <- H. constructor.
    inversion H. simpl. reflexivity.
    simpl in H. remember (fold l1 f def) as frem. symmetry in Heqfrem. apply IHl1 in Heqfrem. rewrite <- H.
    constructor. assumption.
    inversion H. simpl. apply IHl1 in H5. rewrite H5. reflexivity.
Qed.

Fixpoint map {X Y:Type} (l1:list X) (f:X->Y) : list Y :=
  match l1 with
  | nil => nil
  | (cons x lrem) => cons (f x) (map lrem f)
  end.

Definition filter {X:Type} (l:list X) (f:X->bool) : list X :=
  fold l (fun (x:X)=>(fun (l':list X)=>match (f x) with
          | true => (cons x l')
          | false => l' end)) nil.

Definition isNone {X:Type} (x:@Option X) : bool :=
  match x with
  | None => true
  | _ => false
  end.

Definition pushOneNumbered {X:Type} (def:nat) (x:X) (l:list (nat*X)) : (list (nat*X)) :=
  match l with
  | nil => (cons (def,x) nil)
  | (cons (n,x') lrem) => (cons ((S n),x) l)
  end.

Definition numberList {X:Type} (def:nat) (l:list X) : list (nat*X) :=
  fold l (pushOneNumbered def) nil.

Fixpoint twoRev {X:Type} (l1 l2:list X) : list X :=
  match l1 with
  | nil => l2
  | cons x l1rem => twoRev l1rem (cons x l2)
  end.

Definition fastRev {X:Type} (l:list X) : list X :=
  twoRev l nil.

Inductive forAllList {A:Type} : list A -> (A -> Prop) -> Prop :=
  | forAllNil : forall (rel:A->Prop), forAllList nil rel
  | forAllCons : forall (x:A) (lst:list A) (rel:A->Prop), rel x ->
     (forAllList lst rel) -> (forAllList (cons x lst) rel).

Theorem two_rev_pres : forall {X:Type} (l1 l2:list X) P, (forAllList l1 P /\ forAllList l2 P) <->
  forAllList (twoRev l1 l2) P.
Proof.
  split.
  generalize dependent l2.
  induction l1; intros; inversion H. simpl. assumption.
  simpl. inversion H0. apply IHl1. split; try assumption. constructor; assumption.
  intro.
    generalize dependent l2. induction l1; intros. split. constructor. simpl in H. assumption.
    simpl in H. apply IHl1 in H. inversion H. inversion H1. split; try constructor; assumption.
Qed.

Fixpoint tempApp {X:Type} (l1 l2:list X) : list X :=
  match l1 with
  | nil => l2
  | (cons hd tl) => (cons hd (tempApp tl l2))
  end.

Theorem tempAppNil : forall {X:Type} (l:list X), tempApp l nil = l.
Proof.
  induction l; eauto.
  simpl. rewrite IHl. auto.
Qed.

Theorem tempAppAssoc : forall {X:Type} (l1 l2 l3:list X), tempApp l1 (tempApp l2 l3) = tempApp (tempApp l1 l2) l3.
Proof.
  induction l1; intros.
  simpl. reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Theorem temp_App_Mid_Val : forall {X:Type} l1 (a:X) l2, tempApp l1 (cons a l2) = tempApp (tempApp l1 (cons a nil)) l2.
Proof.
  induction l1; intros; simpl. reflexivity.
  rewrite IHl1. reflexivity.
Qed.

Theorem two_rev_app : forall {X:Type} (l1 l2:list X), twoRev l1 l2 = tempApp (twoRev l1 nil) l2.
Proof.
  induction l1; intros.
  simpl. reflexivity.
  simpl. rewrite IHl1. remember (twoRev l1 nil) as tmp. rewrite IHl1.
  apply temp_App_Mid_Val.
Qed.


Theorem two_rev_dist : forall {X:Type} (l1 l2 l3:list X), twoRev (tempApp l1 l2) l3 = tempApp (tempApp (twoRev l2 nil) (twoRev l1 nil)) l3.
Proof.
  induction l1; intros.
  simpl. rewrite <- two_rev_app. apply two_rev_app.
  simpl. rewrite IHl1. rewrite  <- tempAppAssoc. rewrite  <- tempAppAssoc.
  assert(H:tempApp (twoRev l1 []) (a::l3) = tempApp (twoRev l1 [a]) l3).
    rewrite temp_App_Mid_Val. rewrite <- two_rev_app. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem rev_pres : forall {X:Type} (l:list X) P , forAllList l P <-> forAllList (fastRev l) P.
Proof.
  intros.
  split; unfold fastRev; intro. apply two_rev_pres. split. assumption. constructor.
  apply two_rev_pres in H. inversion H. assumption.
Qed.
  

(**

* Arithematic Theorems

Following theorems are proved for later purpose
- forall n, 0 < (S n)
- forall n m, n <= m -> S n <= S m
- forall n m, n < m -> S n < S m
- forall n m, S n <= S m -> n <= m
- forall n m, S n < S m -> n < m

*)

Theorem zero_lt_S_n : forall n, 0 < S n.
Proof.
  induction n.
  econstructor.
  inversion IHn.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  auto.
Qed.

Theorem n_m_le_Sn_Sm : forall p q, p <= q -> S p <= S q.
Proof.
  intros.
  generalize dependent p.
  induction q; intros.
  inversion H; auto.
  inversion H; auto.
Qed.

Theorem n_m_lt_Sn_Sm : forall p q, p < q -> S p < S q.
Proof.
  intros.
  inversion H; auto.
  econstructor.
  apply n_m_le_Sn_Sm.
  assumption.
Qed.

Theorem Sn_Sm_le_n_m : forall p q, S p <= S q -> p <= q.
Proof.
  intros.
  generalize dependent p.
  induction q; intros.
  inversion H; eauto.
  inversion H1.
  inversion H; eauto.
Qed.

Theorem Sn_Sm_lt_n_m : forall p q, S p < S q -> p < q.
Proof.
  intros.
  inversion H.
  econstructor.
  inversion H1.
  econstructor.
  econstructor.
  subst.
  apply Sn_Sm_le_n_m in H1.
  eauto.
Qed.

(**

* Bool coerced as Prop

*)

Inductive boolCoerced : bool -> Prop :=
  | trueP : boolCoerced true.

Theorem forAllListFilter : forall (X Y:Type) (l:list X) (r:X->Prop) (s:X->@Option Y), (forall (x:X), r x -> isNone (s x) = false) ->
  forAllList l r -> filter (map l s) isNone = nil .
Proof.
  induction l.
    intros. simpl. unfold filter. simpl. reflexivity.
    intros. simpl. inversion H0. apply H in H3.
    destruct (s a). unfold filter. simpl.
      replace (fold (map l s)
        (fun (x : Option) (l' : list Option) =>
        if isNone x then (x :: l')%list else l') nil)
      with (filter (map l s) isNone). eapply IHl. apply H. assumption.
      reflexivity.
    inversion H3.
Qed.