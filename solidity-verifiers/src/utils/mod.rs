use crate::{GPL3_SDPX_IDENTIFIER, PRAGMA_GROTH16_VERIFIER};
use askama::Template;
use num_bigint::BigUint;
pub mod encoding;

/// Formats call data from a vec of bytes to a hashmap
/// Useful for debugging directly on the EVM
/// !! Should follow the contract's function signature, we assuming the order of arguments is correct
pub fn get_formatted_calldata(calldata: Vec<u8>) -> Vec<String> {
    let mut formatted_calldata = vec![];
    for i in (4..calldata.len()).step_by(32) {
        let val = BigUint::from_bytes_be(&calldata[i..i + 32]);
        formatted_calldata.push(format!("{}", val));
    }
    formatted_calldata
}

#[derive(Template)]
#[template(path = "header_template.askama.sol", ext = "sol")]
pub struct HeaderInclusion<T: Template> {
    /// SPDX-License-Identifier
    pub sdpx: String,
    /// The `pragma` statement.
    pub pragma_version: String,
    /// The template to render alongside the header.
    pub template: T,
}

impl<T: Template + Default> HeaderInclusion<T> {
    pub fn builder() -> HeaderInclusionBuilder<T> {
        HeaderInclusionBuilder::default()
    }
}

#[derive(Debug)]
pub struct HeaderInclusionBuilder<T: Template + Default> {
    /// SPDX-License-Identifier
    sdpx: String,
    /// The `pragma` statement.
    pragma_version: String,
    /// The template to render alongside the header.
    template: T,
}

impl<T: Template + Default> Default for HeaderInclusionBuilder<T> {
    fn default() -> Self {
        Self {
            sdpx: GPL3_SDPX_IDENTIFIER.to_string(),
            pragma_version: PRAGMA_GROTH16_VERIFIER.to_string(),
            template: T::default(),
        }
    }
}

impl<T: Template + Default> HeaderInclusionBuilder<T> {
    pub fn sdpx<S: Into<String>>(mut self, sdpx: S) -> Self {
        self.sdpx = sdpx.into();
        self
    }

    pub fn pragma_version<S: Into<String>>(mut self, pragma_version: S) -> Self {
        self.pragma_version = pragma_version.into();
        self
    }

    pub fn template(mut self, template: impl Into<T>) -> Self {
        self.template = template.into();
        self
    }

    pub fn build(self) -> HeaderInclusion<T> {
        HeaderInclusion {
            sdpx: self.sdpx,
            pragma_version: self.pragma_version,
            template: self.template,
        }
    }
}
