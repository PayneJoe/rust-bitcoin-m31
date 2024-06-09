#![deny(missing_docs)]

//! This crate defines the gadgets for M31, CM31, and QM31.

/// Module for M31.
mod m31;
pub use m31::*;

/// Module for CM31, the complex extension of M31.
mod cm31;
pub use cm31::*;

/// Module for QM31, a quadratic extension of CM31.
mod qm31;
pub use qm31::*;

/// Module for Karatsuba related algorithm implementations.
mod karatsuba;

pub(crate) mod treepp {
    pub use bitcoin_script::{define_pushable, script};
    #[cfg(test)]
    pub use bitcoin_scriptexec::execute_script;

    define_pushable!();
    pub use bitcoin::ScriptBuf as Script;
}
