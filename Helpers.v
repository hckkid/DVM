(**

Helpers provide few key definitions general for development purpose in Coq.

Option provides support for monads.

*)

Inductive Option {A:Type} : Type :=
  | Some : A -> Option
  | None : Option.

(** 

Fixpoint for equality on naturals.

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

Fixpoint fold {X Y:Type} (l1:list X) (f:X->Y->Y) (def:Y) : Y :=
  match l1 with
  | nil => def
  | (cons x lrem) => (f x (fold lrem f def))
  end.

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

Inductive boolCoerced : bool -> Prop :=
  | trueP : boolCoerced true. 