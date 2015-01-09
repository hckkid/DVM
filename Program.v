Require Export Defs.

(**

* Module Type Declaration for Program

*)

Module Type ProgramType.
  Parameter prg : Type. (* ADT for Program *)
  Parameter getMethods : prg -> list Method.
  Parameter getClasses : prg -> list Class.
  Parameter getFields : prg -> list Field.
End ProgramType.

(**

* Module on Program

This module gives functionality to get classes, methods & fields of given program.

*)

Module PROGRAM <: ProgramType.
  Definition prg := Program.

  Definition getMethods (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => mlst
    end.

  Definition getClasses (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => clst
    end.

  Definition getFields (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => flst
    end.

End PROGRAM.