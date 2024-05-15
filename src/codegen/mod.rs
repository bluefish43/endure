/*!

# The `codegen module`

Functions and structs to make the code generation
compilation phase - which takes HIR and outputs
LLVM bitcode, LLVM IR, binary, object files and
others, possible.

Essentially, here we take the High Level Intermediate Language
generated by the elements in the `check` module (see [`crate::check`])
and generate things from it.

Note that this module does not perform any sanitization or changes
to the High Level Intermediate Language generated by the semantical
check phase, and only generates based on what it's given.

 */

// start

mod llvm;
