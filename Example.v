Add LoadPath "D:\DVM".
Require Export Defs.
Require Export List.
Export ListNotations.
Require Export DvmState.

Open Scope string_scope.

(*

0  == Public
1  == Protected
2  == Private
x>2  == Static && (x-3)

Original Code :-

Public Class super{
public:
  int n[][];
  void super(){
    n = new int[5][6];
  }
}

Public Class sub extends super{
public:
  int p;
  void sub(n:int){
    this.super();
    this.n[0][0] = n;
    p = 30;
  }
}

Public Class tester{
  public static void main(){
    int n;
    super sp = new super();
    inp n;
    sub sb = new sub(n);
    print(sb.n);
  }
}

Intermediate Dalvik Bytecode similar code :-

Classes Indexed
#1 super
#2 sub
#3 tester

MethodSigs
#1 pub super v 100 {}
#2 pub sub v 100 {(n,int)}
#3 static pub main v 100 {}

ClassDecls

{
  pub c1
  ifield f1
  imethod m1
}

{
  pub c2
  ifield f2
  imethod m2
}

{
  pub c3
  smethod m3
}

FieldDecls

#1 n pub (a (a int))  // Two D int array name n public
#2 p pub int

MethodDecls

{
  #1 move r1 5
  #2 move r2 6
  #3 add r3 r1 1
  #4 newarray (sizeda 5 (a int)) r4
  #5 move r5 0
  #6 branch r3 == 0 #12
  #7 newarray (sizeda 6 int) r6
  #8 move r6 (acc r4 r5)
  #9 add r5 r5 1
  #10 sub r3 r3 1
  #11 goto #6
  #12 update (ifield r0 f1) r4
  #13 ret
}

{
  #14 invokei r0 {} m1
  #15 move r1 (ifield r0 f1)
  #16 move r1 (acc r1 0)
  #17 move r1 (acc r1 0)
  #18 update r1 v1
  #19 update (ifield r0 f2) v1
  #20 ret
}

{
  #21 move r1 0
  #22 new r2 #1
  #23 invokei r2 {} m1
  #24 read int r3
  #25 new r4 #2
  #26 invokei r4 {r3} m2
  #27 print int (ifield r4 f2)
  #28 ret
}

*)

Definition cnls : list ClassName := [ "super" ; "sub" ; "tester" ].

Definition msigs : list MethodSig := 
[ (ms 0 "super" v 100 []) ;
  (ms 0 "sub" v 100 [(p(Int),"n")]) ;
  (ms 3 "main" v 100 []) ].

Definition clst : list Class :=
[
  top;
  (class 0 0 [1] [1]) ;
  (class 0 1 [2] [2]) ;
  (class 0 0 [] [3])
].

Definition flst : list Field :=
[
  (fld 0 "n" (r (a (r (a (p Int)))))) ;
  (fld 0 "p" (p Int))
].

Definition mb1 : list (ProgramCounter*Instruction) :=
[
  (1,move 1 (cs (cnat 5))) ;
  (2,move 2 (cs (cnat 6))) ;
  (3,binaryArith 3 (l (reg 2)) badd (cs (cnat 5)));
  (4,newarr 4 (r (a (r (a (p Int))))) (cs (cnat 5)));
  (5,move 5 (cs (cnat 0)));
  (6,branch (l (reg 3)) beq (cs (cnat 0)) 12);
  (7,newarr 6 (r (a (p Int))) (cs (cnat 6)));
  (8,move 7 (cs (cnat 5)));
  (9,update (l (acc 4 7)) (l (reg 6)));
  (10,binaryArith 5 (l (reg 5)) badd (cs (cnat 1)));
  (11,binaryArith 3 (l (reg 3)) bsub (cs (cnat 1)));
  (12,goto 6);
  (13,update (l (reg 4)) (l (ifield 0 1)));
  (14,ret)
].

Definition mb2 : list (ProgramCounter*Instruction) :=
[
  (15,invokei 0 [] 0);
  (16,move 1 (l (ifield 0 1)));
  (17,move 2 (cs (cnat 0)));
  (16,move 1 (l (acc 1 2)));
  (17,move 1 (l (acc 1 2)));
  (18,update (l (reg 1)) (l (reg 101)));
  (19,update (l (ifield 0 2)) (l (reg 101)));
  (20,ret)
].

Definition mb3 : list (ProgramCounter*Instruction) :=
[
  (21,move 1 (cs (cnat 0)));
  (22,new 2 1);
  (23,invokei 2 [] 0);
  (24,read (p Int) 3);
  (25,new 4 2);
  (26,invokei 4 [(l (reg 3))] 1);
  (27,print (p Int) (l (ifield 4 2)));
  (28,ret)
].

Definition mlst : list Method := [ (mtd 1 (mb mb1)) ; (mtd 2 (mb mb2)) ; (mtd 3 (mb mb3)) ].

Definition p : Program := (prog cnls msigs clst flst mlst).

Definition currFrame : Frame := frm [(0,(prim (int 1)));(2,(prim (char 3)));(1,(prim (int 2)))] 2  21.
Definition currHeap : Heap := [].
Definition currSHeap : SHeap := [].
Definition bufferIn : Buffer := (0,[]).
Definition bufferOut : Buffer := (1,[]).

Definition currState : DVMState := dst [currFrame] currHeap currSHeap bufferIn bufferOut.