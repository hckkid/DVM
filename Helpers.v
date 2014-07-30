(**

Helpers provide few key definitions general for development purpose in Coq.

* Option

*)

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
- mod : n1 % n2 , modulo operator

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