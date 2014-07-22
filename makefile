COQBIN:=C:\\Program Files\ \(x86\)\\Coq\\bin\\
Files:=Helpers.v\
	Primitives.v\
	DList.v\
	Defs.v\
	Program.v\
	DvmState.v\
	Method.v\
	Eval.v\
	Type.v\
	Example.v\
	Instructions.v

run:
	$(COQBIN)coqc
	
	
coqc Helpers.v Primitives.v DList.v	Defs.v Program.v DvmState.v Method.v Eval.v Type.v Example.v Instructions.v


