Require Export GenericState.

Declare Module DvmState : GenericStateType with Definition Val' := Val with Definition arrOrObj' := arrOrObj.  
Export DvmState.
Definition DVMState : Type := State.