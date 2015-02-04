Require Export Defs.
Require Export DList.
Require Export Bvector.
Require Export GenericState.

Open Scope type_scope.

Module Type IDvmStateType.

Parameter n:nat.

Definition securityVectorType : Type := Bvector n.

Definition plusSecurityVectors := BVor n.

Definition nullSecurityVector := 

Inductive ObjectVectorType : Type :=
  | topObjVect : securityVectorType -> ObjectVectorType
  | obj : ClassLocation -> ClassLocation -> list (FieldLocation * securityVectorType) -> ObjectVectorType
  | dobjVect : securityVectorType -> ObjectVectorType.

Inductive ArrayVectorType : Type :=
  | arr : nat -> list securityVectorType -> ArrayVectorType.

Inductive arrOrObj' : Type :=
  | ar : ArrayVectorType -> arrOrObj'
  | dob : ObjectVectorType -> arrOrObj'.

Declare Module IDvmStateModule : GenericStateType with Definition Val' := securityVectorType with Definition arrOrObj' := arrOrObj.  
Export IDvmStateModule.

End IDvmStateType.