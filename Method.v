Require Export Program.
Require Export Defs.
Require Export DList.

Open Scope type_scope.

(**

* Overview

This is pretty simple module like Program. We have module signature then module with very few functions.

*)

(**

** MethodType Signature

*)

Module Type MethodType.
  Parameter mthd : Type.
  Parameter prg : Type.
  Parameter getMethod : MethodLocation -> prg -> @Option mthd.
  Parameter firstPC : MethodLocation -> prg -> @Option ProgramCounter.
  Parameter getInstAt : ProgramCounter -> mthd -> @Option Instruction.
  Parameter getNextPC : ProgramCounter -> mthd -> @Option ProgramCounter.
End MethodType.

(**

** Method Module

*)

Module METHOD <: MethodType.
(**

Lets sum this up quickly
- mthd, prg are ADTS for Method and Program
- comp to compare programcounter
- MLIST, MTLIST list module declarations with type ProgramCounter*Instruction and Method respectivly
- getMethod, finds method in program at given method location
- firstPC, returns first ProgramCounter of given method
- getInstAt, return instruction at first occurence of program counter in a method
- getNextPC, return ProgramCounter of next ProgramCounter,Instruction pair after first occurence of input 
  ProgramCounter in given Method

*)
  Definition mthd := Method.
  Definition prg := Program.
  Fixpoint comp (n1 n2:(ProgramCounter*Instruction)) : bool :=
    match n1,n2 with
    | (x1,_),(x2,_) => areEqualNum x1 x2
    end.
  Declare Module MLIST : ListType with Definition t1 := (ProgramCounter * Instruction).
  Declare Module MTLIST : ListType with Definition t1 := Method.
  Definition getMethod (ml:MethodLocation) (pr:prg) : @Option mthd :=
    match pr with
    | (prog cnls msigs clst flst mlst) => (MTLIST.get ml mlst)
    end.
  Definition firstPC (ml:MethodLocation) (p:prg) : @Option ProgramCounter :=
    match (getMethod ml p) with
    | Some (mtd _ (mb (cons (pc1,i1) reminst))) =>Some pc1
    | _ => None
    end.
  Definition getInstAt (p:ProgramCounter) (m:mthd) : (@Option Instruction) :=
    match m with
    | (mtd _ (mb insts)) => match (MLIST.find (p,nop) comp insts) with
      | Some n => match (MLIST.get n insts) with
        | Some (pc,i) => Some i
        | _ => None
        end
      | None => None
      end
    end.
  Definition getNextPC (p:ProgramCounter) (m:mthd) : @Option ProgramCounter :=
    match m with
    | (mtd _ (mb insts)) => match (MLIST.find (p,nop) comp insts) with
      | Some n => match (isle_num (n+1) (MLIST.len insts)) with
        | true => match (MLIST.get (n+1) insts) with
          | Some (pc,i) => Some pc
          | None => None
          end
        | false => None
        end
      | None => None
      end
    end.
End METHOD.