//! Simple proc-macro like tokenizer

#![no_std]
#![deny(missing_docs)]

extern crate alloc;

mod location;
mod token;
mod tree;

pub use location::*;
pub use token::*;
pub use tree::*;
