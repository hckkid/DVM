(**

* Heap Soundness

Heap Soundness property states that given all refrences are to allocated locations only in a given state,
next state after executing an instruction will still have refrences to allocated instructions only.
It is kind of similar to preservation property for CoqDVM.

* Debugging Mode

The reason we made use of deltaState was in order to allow for a debugging mode, where you can take control of machine,
And easily change machine states without having to modify program.

* Security Aspects

We would like to do security analysis on a program, like the way it is done in ScanDal, so as to know if there are
security leaks in bytecode or not.

* Completeness

Making use of Occam's Razor we will be able to state after incorporating few more instructions that our subset is
as complete as DVM. Right now we are 7 instructions behind of which 3 are nearly achieved, 2 are for concurrency.

*)