/*!

# The `llvm` module

This module just is the one which manages the
context, module and builder of the code generation.

 */

use derive_getters::Getters;
use inkwell::{builder::Builder, context::Context, module::Module};

/// Holds core structures for the interaction
/// with LLVM.
pub struct Holder<'c> {
    context: &'c Context,
    module: Module<'c>,
    builder: Builder<'c>,
}

impl<'c> Holder<'c> {
    /// Constructs a new `Holder`.
    pub fn from_context(context: &'c Context, module_name: &str) -> Self {
        Self {
            context,
            module: context.create_module(module_name),
            builder: context.create_builder(),
        }
    }

    pub fn context(&self) -> &Context {
        &self.context
    }

    pub fn module(&self) -> &Module<'c> {
        &self.module
    }

    pub fn builder(&self) -> &Builder<'c> {
        &self.builder
    }
}
