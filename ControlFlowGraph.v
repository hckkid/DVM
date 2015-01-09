Require Export BasicBlock.

Module Type CFGType.

Parameter toPaths : nat -> nat -> list (bool*(list nat)) -> list (list nat).

End CFGType.

Module CFG <: CFGType.

Fixpoint nthBlockEdges (blk:nat) (graph:list (bool*(list nat))) : bool*(list nat) :=
  match blk with
  | O => (false,[])
  | S O => match graph with 
    | [] => (false,[])
    | g::gs => g
    end
  | S (S n) => match graph with
    | [] => (false,[])
    | g::gs => nthBlockEdges (S n) gs
    end
  end.

Fixpoint visitNthBlock (blk:nat) (graph:list (bool*(list nat))) : (list (bool*(list nat))) :=
  match blk with
  | 0 => graph
  | S O => match graph with
    | [] => []
    | (_,lst)::gs => (true,lst)::gs
    end
  | S (S n) => match graph with
    | [] => []
    | g::gs => g::(visitNthBlock (S n) gs)
    end
  end.

Fixpoint toAcyclicUptoNPaths (n:nat) (blk:nat) (graph:list (bool*(list nat))) : list (list nat) :=
  match n with
  | O => [[]]
  | (S n) => match blk with
    | O => [[O]]
    | _ => match (nthBlockEdges blk graph) with
      | (true,_) => [[]]
      | (false,lst) => (fold (map lst (fun x => 
        (map (toAcyclicUptoNPaths n x (visitNthBlock blk graph)) (fun y=>blk::y))))
        (fun x => fun y => fold x (fun x2 => fun y2 => x2::y2) y) [])
      end
    end
  end.

Definition pathsWith (blk:nat) (paths:list (list nat)) : list (list nat) :=
  filter paths (fun x => findIf x (areEqualNum blk)).

Fixpoint uptoBlockIn (blk:nat) (path:list nat) : list nat :=
  match path with
  | [] => []
  | x::xs => match areEqualNum x blk with
    | true => []
    | false => x::(uptoBlockIn blk xs)
    end
  end.

Definition uptoBlock (blk:nat) (paths:list (list nat)) : list (list nat) :=
  map paths (uptoBlockIn blk).

Definition toPathsAcyc (blk:nat) (graph:list (list nat)) : list (list nat) := 
  (toAcyclicUptoNPaths (S (length graph)) blk (map graph (fun x=>(false,x)))).

(* Must handle case of 0 paths i.e. dead code/ stuck code*)

Definition sdom (blks:list nat) (graph:list (list nat)) (paths:list (list nat)) : list (nat*(list nat)) :=
  map blks (fun blk =>
  (blk,(fold (uptoBlock blk (pathsWith blk paths))
  (fun x=> fun y=>intersection x y areEqualNum)
  (nToZero (length graph))))).

Definition findSdom (blk:nat) (sd:list (nat*(list nat))) : list nat :=
  fold sd (fun x=>fun y=>match x with | (x1,x2) => match (areEqualNum x1 blk) with | true => x2 | false => y end end) [].

Definition idom (blks:list nat) (graph:list (list nat)) (paths:list (list nat)) : list (nat*(list nat)) :=
  (fun sd=>map blks (fun blk=>(blk,((fun ls=>fold (map ls (fun x=>findSdom x sd)) (fun x => fun y=>difference y x areEqualNum) ls) (findSdom blk sd)))))
  (sdom blks graph paths).

Definition fdom (blks:list nat) (graph:list (list nat)) : list (nat*(list nat)) :=
  map blks (fun blk=>(blk,difference ((fun paths=>(fold paths (fun x=>fun y=>intersection x y areEqualNum) 
    (match paths with | [] => [] | _ => (nToZero (length graph)) end)))
    (toPathsAcyc blk graph))
    [blk] areEqualNum)).

Definition findFdom (blk:nat) (fd:list (nat*(list nat))) : list nat :=
  fold fd (fun x=>fun y=>match x with | (x1,x2) => match (areEqualNum x1 blk) with | true => x2 | false => y end end) [].

Definition ifdom (blks:list nat) (graph:list (list nat)) : list (nat*(list nat)) :=
  (fun fd=>map blks (fun blk=>(blk,(fun ls=> fold ls (fun x=> fun y=> difference y (findFdom x fd) areEqualNum) ls) (findFdom blk fd))))
  (fdom blks graph).

Definition tripFrom (blk:nat) (path:list nat) := match (fold path (fun x=> fun y=> match (areEqualNum x blk),y with
  | true,(_,y1) => (x::y1,[])
  | false,(y1,y2) => (y1,x::y2) end) ([],[])) with | (y1,y2) => y2 end.

Fixpoint toPaths2 (n:nat) (blk:nat) (graph:list (bool*(list nat))) : list (list (bool*(list nat))) :=
  match n with
  | O => [graph]
  | (S n) => match blk with
    | O => [graph]
    | _ => match (nthBlockEdges blk graph) with
      | (true,_) => []
      | (false,lst) => (fold (map lst (fun x => 
        (toPaths2 n x (visitNthBlock blk graph))))
        (fun x => fun y => fold x (fun x2 => fun y2 => x2::y2) y) [])
      end
    end
  end.

Require Export Example.

Definition tillIfDom (blks:list nat) (graph:list (list nat)) : list (nat*(list nat)) := (fun ifd => (map blks (fun blk=> (fun paths =>
  (blk,(fold (fold (findFdom blk ifd) (fun dom=>uptoBlock dom) paths) (fun x=>fun y=> x++y )[]))) 
  (map (toPathsAcyc blk graph) (fun x=>difference x [blk] areEqualNum)))))
  (ifdom blks graph).

Compute (tillIfDom [1;2;3;4;0;0] (BasicBlock.toBlocks3 mb1)).

Definition g1 := map (BasicBlock.toBlocks3 mb1) (fun x => (false,x)).

Compute (pathsWith 4 (toAcyclicUptoNPaths 6 1 g1)).