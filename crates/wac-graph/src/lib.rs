//! A library for defining and encoding WebAssembly composition graphs.

#![deny(missing_docs)]

pub(crate) mod encoding;
mod graph;

pub use graph::*;
