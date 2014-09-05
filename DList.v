Add LoadPath "D:\DVM".
Require Export Helpers.

(**

* Overview

We deviated from out past approach on use of modules here slightly, that is because previously
we were using Moudles for functionality only, now we want a module functor which given some parameter
can provide us with a specific module based on given parameter. Why do we need this?

- Frame : it is a product of (Register Value pairs) , MethodLocation and Program Counter, we need a list module for Register Value pairs
- Heap : it is a list of arrOrObj, so now we need a list module on ADT arrOrObj
- SHeap : it is a list of FieldLocation*Val, so again another list module with another type
- Array : in arr object we have a list of Val
- Object : in object we have list of FieldLocation*Val for instance fields

So this pretty much sums up why we have a "Module Type" with implementation instead of "Module" , this allows
us to declare any Module extending this type with t1 declared to have full functionality implemented here.

*)

Module Type ListType.

(**

** Construtor and ADT declarations

*)
  Parameter t1 : Type.
  Definition t2 := list t1.
  Definition empty : t2 := nil.
  Definition app (x:t1) (l:t2) := (cons x l).

(**

* Operations

We have numrous operations on list coded up just in case needs be, but following operations are most frequently used:
- find : finds a value in list based upon input compare function
- get : fetch the value at input location
- set : set input value at input location
- setMany : multiple set operations with inputs provided as location value pairs
- prep : puts a new value at the end of list
- find_in_range : find always returns allocated location if a location is returned
We have every definition followed by its relations equivalent and theorem showing the equivalence.

*)

  Fixpoint remove (x:t1) (comp:t1 -> t1 -> bool) (l:t2) :=
    match l with
    | nil => nil
    | (cons x' ls) => match (comp x x') with
      | true => (remove x comp ls)
      | false => (cons x' (remove x comp ls))
      end
    end.
  Fixpoint find (x:t1) (comp:t1 -> t1 -> bool) (l:t2) : (@Option nat) :=
    match l with
    | nil => None
    | (cons x' ls) => match (comp x x') with
      | true => (Some 0)
      | false => match (find x comp ls) with
        | None => None
        | Some n => Some (S n)
        end
      end
    end.
  Fixpoint get (n:nat) (l:t2) : @Option t1 :=
    match n,l with
    | _,nil => None
    | 0,(cons hd tl) => Some hd
    | (S n),(cons hd tl) => (get (n) tl)
    end.
  Fixpoint set (n:nat) (x:t1) (l:t2) : t2 :=
    match n,l with
    | _,nil => nil
    | 0,(cons x' ls) => (cons x ls)
    | (S n),(cons x' ls) => (cons x' (set n x ls))
    end.
  Fixpoint prep (x:t1) (l:t2) : t2 :=
    match l with
    | nil => (cons x nil)
    | (cons x' ls) => (cons x' (prep x ls))
    end.
  Fixpoint len (l:t2) : nat :=
    match l with
    | nil => 0
    | (cons x' ls) => S (len ls)
    end.
  Fixpoint rev (l:t2) : t2 :=
    match l with
    | nil => nil
    | (cons x' ls) => prep x' (rev ls)
    end.
  Fixpoint norepeat (comp:t1 -> t1 -> bool) (l:t2) : bool :=
    match l with
    | nil => true
    | (cons x' ls) => match (find x' comp ls) with
      | None => (norepeat comp ls)
      | _ => true
      end
    end.
  Fixpoint setMany (vals:list (nat*t1)) (lst:t2) : t2 :=
    match vals with
    | nil => lst
    | (cons (n1,val1) rem) => setMany rem (set n1 val1 lst)
    end.

(**

* Key Theorems

Although we are proving theorems for list, but these meta theorems appear as-is if we had separate heap module,
Only program and state dependent heap properties would need to be defined later. Here is a list of theorems

- prep_rev : reverse after prep is same as cons to reverse of original list
- rev_rev_same : reverse of reverse is always original list
- get_nil : get of nil is None
- get_set_avail : get after a set at allocated location is always the value input in set
- get_set_unavail : get after a set at unallocated location is always None
- get_set_indep : get at location independent of set remains the same
- get_set_dep : get at location same as set changes to input value in set
- get_find : get after a find is successful.

*)

  Theorem prep_rev : forall a lst, rev (prep a lst) = cons a (rev lst).
  Proof.
    intros.
    induction lst.
    auto.
    simpl.
    rewrite IHlst.
    simpl.
    reflexivity.
  Qed.

  Theorem rev_rev_same : forall lst:t2, rev (rev lst) = lst.
  Proof.
    induction lst.
    auto.
    simpl.
    rewrite prep_rev.
    rewrite IHlst.
    reflexivity.
  Qed.

  Theorem get_nil : forall n, get n nil = None.
  Proof.
    intros; destruct n; auto.
  Qed.

  Theorem get_avail : forall n lst, n<len lst -> exists v, get n lst = Some v.
  Proof.
    intros n lst. generalize dependent n. induction lst.
    destruct n. simpl. intros. inversion H.
      simpl. intros. inversion H.
    destruct n. simpl. intros. exists a. reflexivity.
      simpl. intros. apply Sn_Sm_lt_n_m in H. apply IHlst. assumption.
  Qed.

  Theorem get_set_avail : forall n v lst, n < (len lst) -> get n (set n v lst) = Some v.
  Proof.
    intros.
    generalize dependent n.
    induction lst; simpl; intros.
    inversion H.
    destruct n; auto.
    simpl.
    apply IHlst.
    apply Sn_Sm_lt_n_m.
    auto.
  Qed.

  Theorem get_set_unavail : forall n v lst, ~ (n < (len lst)) -> get n (set n v lst) = None.
  Proof.
    induction n.
    destruct lst; intros.
    auto.
    simpl in H. assert False.
    apply H. apply zero_lt_S_n.
    inversion H0.
    intros.
    destruct lst.
    auto.
    simpl.
    assert (~ (n < len lst)).
    intro Contra.
    apply H.
    simpl.
    apply n_m_lt_Sn_Sm. assumption.
    apply IHn.
    assumption.
  Qed.

  Theorem find_in_range : forall x cmp lst n1, ( find x cmp lst ) = Some n1 -> n1 < (len lst).
  Proof.
    intros.
    generalize dependent n1.
    induction lst; intros; inversion H.
      destruct (cmp x a).
        inversion H1.
        simpl.
        apply zero_lt_S_n.
        destruct (find x cmp lst).
          inversion H1.
          simpl.
          apply n_m_lt_Sn_Sm.
          apply IHlst.
          reflexivity.
          inversion H1.
  Qed.    

  Theorem find_set_get : forall x cmp lst n1 v, ( find x cmp lst ) = Some n1 -> get n1 (set n1 v lst) = Some v.
  Proof.
    intros.
    apply find_in_range in H.
    apply get_set_avail.
    assumption.
  Qed.

  Theorem get_set_indep : forall n n' v v' lst, n<>n' -> get n lst = Some v -> get n (set n' v' lst) = Some v.
  Proof.
    intros.
    generalize dependent n.
    generalize dependent n'.
    induction lst; intros.
    destruct n; inversion H0.
    destruct n; destruct n'.
      assert False.
        apply H. reflexivity.
        inversion H1.
      simpl. simpl in H0. assumption.
      simpl. simpl in H0. assumption.
      simpl. simpl in H0. apply IHlst.
        intro Contra. apply H. rewrite Contra. reflexivity.
        assumption.
  Qed.

  Theorem get_set_dep : forall n n' v v' lst, n=n' -> get n lst = Some v -> get n (set n' v' lst) = Some v'.
  Proof.
    intros.
    generalize dependent n.
    generalize dependent n'.
    induction lst; intros.
    destruct n; inversion H0.
    destruct n; subst.
      auto.
      simpl. apply IHlst; auto.
  Qed.

  Inductive compRel : (t1->t1->bool) -> t1 -> t1 -> Prop :=
    | fRel : forall (cmp:(t1->t1->bool)) (inp1:t1) (inp2:t1), (boolCoerced (cmp inp1 inp2)) -> compRel cmp inp1 inp2.

  Theorem compEq : forall (x1 x2:t1) (cmp:t1->t1->bool), (cmp x1 x2 = true) <-> compRel cmp x1 x2.
  Proof.
    intros.
    split; intro.
      econstructor. rewrite H. constructor.
      inversion H. inversion H0. reflexivity.
  Qed.

  Inductive findRel : t1 -> (t1 -> t1 -> bool ) -> t2 -> (@Option nat) -> Prop :=
    | currFindRel : forall (x x2:t1) (cmp:t1->t1->bool) (rem:t2), compRel cmp x x2 -> findRel x cmp (cons x2 rem) (Some 0)
    | remFindRel : forall (x x2:t1) (cmp:t1->t1->bool) (rem:t2) (n:nat), ~(compRel cmp x x2) -> findRel x cmp rem (Some n) -> findRel x cmp (cons x2 rem) (Some (S n))
    | nilFindRelNone : forall (x:t1) (cmp:t1->t1->bool), findRel x cmp nil None
    | remFindRelNone : forall (x x2:t1) (cmp:t1->t1->bool) (rem:t2), ~(compRel cmp x x2) -> findRel x cmp rem None -> findRel x cmp (cons x2 rem) None.

  Theorem findRelEq : forall (x:t1) (cmp:t1->t1->bool) (lst:t2) (res:@Option nat),(findRel x cmp lst res) <-> (find x cmp lst = res).
  Proof.
    induction lst; split; intro.
    inversion H; simpl; reflexivity.
    simpl in H; subst; econstructor.
    inversion H; subst; simpl; remember (cmp x a) as cmpres; destruct cmpres; auto.
      inversion H5. rewrite <- Heqcmpres in H0. inversion H0.
      assert(False). apply H4. econstructor. rewrite <- Heqcmpres. econstructor. inversion H0.
      apply IHlst in H6. rewrite H6. reflexivity.
      assert(False). apply H4. econstructor. rewrite <- Heqcmpres. econstructor. inversion H0.
      apply IHlst in H6. rewrite H6. reflexivity.
    simpl in H; remember (cmp x a) as cmpres; destruct cmpres.
      subst; econstructor. econstructor. rewrite <- Heqcmpres. econstructor.
      destruct (find x cmp lst); subst; econstructor; try (intro; inversion H; inversion H0; rewrite <- Heqcmpres in H5; inversion H5); try (eapply IHlst; reflexivity).
  Qed.

  Inductive getRel : nat -> t2 -> @Option t1 -> Prop :=
    | zeroGetRel : forall (x:t1) (lst:t2), getRel 0 (cons x lst) (Some x)
    | succGetRel : forall (n:nat) (x y:t1) (lst:t2), getRel n lst (Some x) -> getRel (S n) (cons y lst) (Some x)
    | nilGetRelNone : forall (n:nat), getRel n nil None
    | consGetRelNone : forall (n:nat) (lst:t2) (x:t1), getRel n lst None -> getRel (S n) (cons x lst) None.

  Theorem getRelEq : forall (n:nat) (x:@Option t1) (lst:t2), getRel n lst x <-> get n lst = x.
  Proof.
    induction n.
    split; intro.
      inversion H; simpl; reflexivity.
      destruct lst; simpl in H; subst; econstructor.
    split; intro.
      inversion H; simpl; auto; apply IHn; auto.
      destruct lst; simpl in H; subst; try econstructor.
        remember (get n lst) as gtlst. destruct gtlst; econstructor; eapply IHn; symmetry; assumption.
  Qed.

  Inductive setRel : nat -> t1 -> t2 -> t2 -> Prop :=
    | nilSet : forall (n:nat) (x:t1), setRel n x nil nil
    | currConsSet : forall (x y:t1) (lst:t2), setRel 0 x (cons y lst) (cons x lst)
    | succConsSet : forall (n:nat) (x y:t1) (lst lst':t2), setRel n x lst lst' -> setRel (S n) x (cons y lst) (cons y lst').

  Theorem setRelEq : forall (n:nat) (x:t1) (lst lst':t2), (set n x lst = lst') <-> (setRel n x lst lst').
  Proof.
    intros n x lst.
    generalize dependent n.
    generalize dependent x.
    induction lst; split; intro.
      destruct n; simpl in H; subst; econstructor.
      inversion H. destruct n; simpl; reflexivity.
      destruct n; simpl in H; subst; econstructor. apply IHlst. reflexivity.
      inversion H. simpl. reflexivity. simpl. subst.
        assert(set n0 x lst = lst'0). apply IHlst. assumption.
        rewrite H0. reflexivity.
  Qed.

  Inductive prepRel : t1 -> t2 -> t2 -> Prop :=
    | nilPrep : forall (x:t1), prepRel x nil (cons x nil)
    | consPrep : forall (x y:t1) (rem1 rem2:t2), prepRel x rem1 rem2 -> prepRel x (cons y rem1) (cons y rem2).

  Theorem prepRelEq : forall (x:t1) (lst lst':t2), prep x lst = lst' <-> prepRel x lst lst'.
  Proof.
    intros x lst.
    generalize dependent x.
    induction lst; split; intro.
      simpl in H; subst; econstructor.
      inversion H; subst; simpl; reflexivity.
      simpl in H. destruct lst'; inversion H. econstructor. apply IHlst. reflexivity.
      inversion H; subst; simpl. apply IHlst in H4. rewrite H4. reflexivity.
  Qed.

  Inductive setManyRel : list (nat*t1) -> t2 -> t2 -> Prop :=
    | nilSetManyRel : forall (lst:t2), setManyRel nil lst lst
    | consSetManyRel : forall (lst1 lst2 lst3:t2) (x:nat) (v1:t1) (rem:list (nat*t1)),
                        setRel x v1 lst1 lst2 -> setManyRel rem lst2 lst3 ->
                        setManyRel (cons (x,v1) rem) lst1 lst3.

  Theorem setManyRelEq : forall (data:list (nat*t1)) (lst1 lst2:t2), setMany data lst1 = lst2 <-> setManyRel data lst1 lst2.
  Proof.
    induction data;
    split; intro.
      simpl in H. subst; try econstructor.
      inversion H. simpl. reflexivity.
      simpl in H. subst. destruct a. remember (set n t lst1) as lst2. econstructor.
        eapply setRelEq. symmetry. eapply Heqlst2.
        apply IHdata. reflexivity.
      inversion H. simpl. apply setRelEq in H2. rewrite H2. apply IHdata. assumption.
  Qed.

  Theorem get_find : forall (x:t1) (n:nat) (cmp:t1->t1->bool) (lst:t2), find x cmp lst = Some n -> (exists y,get n lst = Some y).
  Proof.
    intros x n cmp lst.
    generalize dependent n.
    induction lst. simpl. intros. inversion H.
    intros. simpl in H.
    destruct (cmp x a).
      inversion H. subst. simpl. exists a. reflexivity.
      destruct (find x cmp lst).
        inversion H; subst. simpl. apply IHlst. reflexivity.
        inversion H.
  Qed.

End ListType.