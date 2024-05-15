/*!

# The `llvm` module

This module just is the one which manages the
context, module and builder of the code generation.

 */

use inkwell::{context::Context, module::Module, builder::Builder};

/// Holds core structures for the interaction
/// with LLVM.
pub struct Holder<'c> {
    context: &'c Context,
    module: Module<'c>,
    builder: Builder<'c>,
}

impl<'c> Holder<'c> {
    /// Constructs a new `Holder`.
    pub fn new(context: &'c Context, module_name: &str) -> Self {
        Self {
            context,
            module: context.create_module(module_name),
            builder: context.create_builder(),
        }
    }
}
