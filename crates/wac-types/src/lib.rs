//! A library for the definition of WebAssembly component model types.

#![deny(missing_docs)]

mod checker;
mod component;
mod core;
mod package;

pub use checker::*;
pub use component::*;
pub use core::*;
pub use package::*;
