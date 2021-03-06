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


for compiling from inside subdirectory

coqc CoqDVM.v Helpers.v Primitives.v DList.v Defs.v Program.v GenericState.v DvmState.v Method.v Eval.v DType.v Example.v Instructions.v Consistency.v Progress.v LookingAhead.v

coqc ..\CoqDVM.v ..\Helpers.v ..\Primitives.v ..\DList.v ..\Defs.v ..\Program.v ..\DvmState.v ..\Method.v ..\Eval.v ..\DType.v ..\Example.v ..\Instructions.v ..\Consistency.v ..\Progress.v ..\LookingAhead.v

for html doc

coqdoc --no-lib-name --toc --html ..\CoqDVM.v ..\Helpers.v ..\Primitives.v ..\DList.v ..\Defs.v ..\Program.v ..\DvmState.v ..\Method.v ..\Eval.v ..\DType.v ..\Example.v ..\Instructions.v ..\Consistency.v ..\Progress.v ..\LookingAhead.v


coqdoc --no-lib-name --toc --tex ..\CoqDVM.v ..\Helpers.v ..\Primitives.v ..\DList.v ..\Defs.v ..\Program.v ..\DvmState.v ..\Method.v ..\Eval.v ..\DType.v ..\Example.v ..\Instructions.v


coqdoc --no-lib-name --toc --pdf ..\CoqDVM.v ..\Helpers.v ..\Primitives.v ..\DList.v ..\Defs.v ..\Program.v ..\DvmState.v ..\Method.v ..\Eval.v ..\DType.v ..\Example.v ..\Instructions.v


