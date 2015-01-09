Require Export DList.
Require Export Method.

Module Type BasicBlockType.

Parameter iinst:Type.

Parameter isBranch : iinst -> bool.
Parameter branchesTo : iinst -> list nat.
Parameter isInstAt : nat -> iinst -> bool.

Parameter allLeaders : list iinst -> list (iinst*bool).

Parameter toBlocks2 : list iinst -> list (list iinst).
Parameter toBlocks3 : list iinst -> list (list nat).

(*Parameter toBlocks : list iinst -> list (list iinst). *)

End BasicBlockType.

Module BasicBlock <: BasicBlockType.

Definition iinst := ProgramCounter*Instruction.

Definition isBranch (x:iinst) : bool :=
  match x with
  | (_,goto _) => true
  | (_,branch _ _ _ _) => true
  | (_,_) => false end.

Definition branchesTo (x:iinst) : list nat :=
  match x with
  | (_,goto pc) => [pc]
  | (pc1,branch _ _ _ pc2) => [S pc1;pc2]
  | (_,ret) => [0]
  | (_,retTo _) => [0]
  | (pc1,_) => [S pc1] end.

Definition branchPairs (l1:list iinst) : list (nat*nat) :=
  fold l1 (fun x => fun y => match x with
    | (pc1,goto pc2) => (pc1,pc2)::y 
    | (pc1,branch _ _ _ pc2) => (pc1,(S pc1))::(pc1,pc2)::y
    | (_,_) => y end) [].

Definition isInstAt := fun y => (fun x:iinst => match x with | (pc1,_) => (areEqualNum y pc1) end).

Definition allBranchesTo (iilst:list iinst) : list nat := fold iilst (fun x=> match (isBranch x) with
      | false => fun y => y
      | true => fun (y:list nat) => ((branchesTo x)++y) end) nil.

Definition augmentAllBool (iilst:list iinst) : list (iinst*bool) := map iilst (fun x=>(x,false)).

Definition updateAt (n:nat) (ibilst:list (iinst*bool)) : list (iinst*bool) := map ibilst
      (fun p => match p with | (x,y) => match isInstAt n x with
        | true => (x,true)
        | false => (x,y) end end).

Definition markLeaders (clst:list nat) (ibilst:list (iinst*bool)) : list (iinst*bool) := fold clst (fun x=>fun y=>
      updateAt x y) ibilst.

Definition markFirst (ibilst:list (iinst*bool)) : list (iinst*bool) := match ibilst with
  | nil => nil
  | x::xrem => match x with | (p1,q1) => (p1,true)::xrem end end.

Definition allLeaders (c:list iinst) : list (iinst*bool) := markFirst (markLeaders (allBranchesTo c) (augmentAllBool c)).

Definition toBlocks1 (clst:list iinst) := match (fold (allLeaders clst) (fun (x:iinst*bool) => fun y:((list iinst)*(list nat))*(list ((list iinst)*(list nat))) => match x,y with 
  | (ins,false),(([],_),l2) => (([ins],(branchesTo ins)),l2)
  | (ins,false),((y::l1,x),l2) => ((ins::y::l1,x),l2)
  | (ins,true),(([],x),l2) => (([],[]),([ins],(branchesTo ins))::l2)
  | (ins,true),((y::l1,x),l2) => (([],[]),((ins::y::l1),x)::l2) end) (([],[]),[]))
  with | (_,blks) => blks end.

Definition findInBlock (blk:list iinst) (pc:nat) := fold blk (fun x=>fun y=>match x with | (pc',_) => orb (areEqualNum pc' pc) y end) false.

Fixpoint findBlock (pc:nat) (blks:list (list iinst)) : nat := match blks with
  | [] => 0
  | blk::brem => match (findInBlock blk pc) with
    | true => S O
    | false => match (findBlock pc brem) with
      | O => O
      | (S n) => S (S n)
      end
    end
  end.

Definition toBlocks2 (clst:list iinst) := map (toBlocks1 clst) (fun x:(list iinst)*(list nat)=>
  match x with
  | (x1,_) => x1 end).

Definition toBlocks3 (clst:list iinst) := map (toBlocks1 clst) (fun x:(list iinst)*(list nat)=>(fun y=>
  match x with
  | (x1,x2) => (fold x2 (fun z=>fun z2=>(findBlock z y)::z2) []) end) (toBlocks2 clst)).

(*Definition blockPairs (cd:list iinst) : list (nat*nat) := map (branchPairs cd) ((fun y:(list (list iinst)) => fun x => match x with
  | (pc1,pc2) => ((findBlock pc1 y),(findBlock pc2 y)) end) (toBlocks cd)).
*)
End BasicBlock.


