Add LoadPath "D:\DVM".
Require Export Defs.

Module Type ProgramType.
  Parameter prg : Type. (* ADT for Program *)
  Parameter getMethods : prg -> list Method.
  Parameter getClasses : prg -> list Class.
  Parameter getFields : prg -> list Field.
End ProgramType.

Module PROGRAM <: ProgramType.
  Definition prg := Program.
<<<<<<< HEAD
  
=======
>>>>>>> master
  Definition getMethods (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => mlst
    end.
<<<<<<< HEAD

=======
>>>>>>> master
  Definition getClasses (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => clst
    end.
<<<<<<< HEAD

=======
>>>>>>> master
  Definition getFields (p:prg) := 
    match p with
    | (prog cnl mnl clst flst mlst) => flst
    end.
<<<<<<< HEAD

=======
>>>>>>> master
End PROGRAM.