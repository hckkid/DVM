Add LoadPath "D:\DVM".
Require Export DList.

Module Type BasicBlockType.

Parameter iinst:Type.
Definition code:= list iinst.

Parameter isBranch : iinst -> bool.
Parameter branchesTo : iinst -> list nat.
Parameter isInstAt : nat -> iinst -> bool.

Definition allBranchesTo (iilst:list iinst) : list nat := fold iilst (fun x=> match (isBranch x) with
      | true => fun y => y
      | false => fun (y:list nat) => ((branchesTo x)++y) end) nil.

Check allBranchesTo.

Definition isBranchProp := (fun x => (isBranch x = true)).
Definition noBranchProp := (fun x => (isBranch x = false)).
Definition noneBranchProp := (fun x => forAllList x noBranchProp).


Definition branchesTo

Check basicblock_rec.

End BasicBlockType.