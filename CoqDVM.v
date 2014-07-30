(**

CoqDVM is a Proof Carrying Code for a subset of Dalvik Virtual Machine (DVM).
This subset of Dalvik Virtual Machine is made keeping Occam's Razor in mind.

* Overview

To begin with, lets take top to bottom view approach. Which means we will go
to deeper level of abstractions after describing top level abstractions.
CoqDVM from topmost view can be broken into following units:
- General Units providing universal functions
- Syntax Defining Units provide syntax used by CoqDVM
- Semantic Defining Units which basically are an implementation for given syntax
- Proof Units formed by files carrying relations and theorems over CoqDVM

** General Units

This part of CoqDVM is made by Helpers Module and DList Module. Both of these files provide
generic functionality. Helper provides functions and definitions as general as Option for monads
fold, map, filter for list operations. List on other hand provides a Parameterised module on lists
with list function alog with their Relation eqvivalents. The benefits of having a relation equivalent
are from proof perspective as they aren't bound by termination coditions, which is key feature writing
multi step relation for CoqDVM. We will discuss this further during Instruction Module which is part
of semantic defining units.

** Syntax Defining Units

This part is formed by modules Primitives Defs Program DvmState and Method.

*** Primitives

Primitives Module defines Primitive types of Coqdoc along with arithmetic over primitives,
Cast & Compare operation on primitives and also fuction to genrate equivalent natural(nat) or
generate primitive provided type and natural. Primitives Modules also hosts definition of
Operators in CoqDVM.

*** Defs

Defs module as the name suggest defines the core syntax of CoqDVM, key definitions worth
mentioning are:
- Constant (Not defined in primitives)
- lhs & rhs (Almost as their name suggest except there is no equality)
- Instruction (Defines Syntax for valid instructions)
- Method, Field, Class (For object oriented features)
- Val (Values that register can hold, allows refrences)
- Object & Array (Semantic Domain for the former in Heap)
- Program (Allowed program definition, note no verification on class/method/field links is done, its done on runtime)

*** Method & Program

These are very small modules, which basically provide few simple operation on their corresponding Semantic Domain.
- Program basically allows one to fetch its constituent Classes, Methods & Fields.
- Method allows to get next program counter provided current counter, getting instruction at given counter etc.

*** DvmState

DvmState is as much part of semantic defining unit as much it is for syntax definitions. In DvmState we
introduce DVMState which is syntax definition for current state of CoqDVM. In DvmState we also
introduce deltaState, which we use to represent unit changes between two DVMState's. So any changes CoqDVM
undergoes on execution of one or more Instructions is mapped into a list of deltaState. Then we finally
introduce mkChange and mkChanges, which determine given a DVMState and deltaState / list deltaState respectively,
the final DVMState based on both these inputs, which CoqDVM should be in.

** Semantic Definining Units

The semantics for CoqDVM is covered by modules DvmState(already described), Eval, DType and Instructions.

*** Eval

Eval module consists mainly of three important fixpoint definitions and their relation equivalents, which are
- evalReg : it take a register location as input followed by current state, and produces value for asked Register
- evalLhs : it takes an expression of semantic domain lhs followed by state producing its computed value
- evalRhs : Just like previous two function this one computes value for expression of domain rhs in a given state.

*** DType

DType modules deals with operations on composite types. It can primarily be said to deal with following three operations

- createObject : returns a newly created object(No constructors called yet) of input type, this definition is used by
  instruction new
- createArray : returns a newly created 1 dimensional array of given type, this definition is used by newarr instrucction
- cast : This instruction does type casting for composite types.

*** Instructions

Instructions modules is a huge module, since it provide semantics for each and every instruction in CoqDVM.
We take tagcode of given instruction, appending its name with eval & first letter capitalised we get name for its
implementation definition. For e.g. : implementation of nop is given in evalNop, branch is given in evalBranch.
Finally we couple all these definition together in single definition evalInst which given an Instruction, current State
and Program returns list deltaState which can be used to compute next State using mkChanges defined in DvmState.
And to add more simplicity we define stepFix and multiStepFix which given State and Program take step based on what
current instruction is, by application of evalInst and mkChanges.

** Proof Units

This part of CoqDVM is still upgrading, currently it consists of modules Example, Consistency and Progress.

*** Consistency

We define inductive definitions of relation which take care of necessities to compute corresponding execution unit.
For example consistentEvalReg n st will have an evidence only if Register n is compuptable in state st.
This makes every consistent Relation over states to have evidence for halt state and never for stuck state.
We define consistency relation for each instruction taking care of its parameters as input and then finally couple
them all as single relation on instruction as consistentInst. Consistency has many uses, primary use for it now is
in Progress property and Heap soundness property.

*** Example

This module is completely optional but we have it for testing purpose. Here we have CoqDVM implementation of a source
Java program which we converted into a sub-dalvik equivalent and then we defined in CoqDVM. We make use of example
file in Instructions module where we use multiStepFix on program and state defined in it.

*** Progress

This module is to prove progress property on CoqDVM and is in development right now.


*)