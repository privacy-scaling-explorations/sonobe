use std::fmt::Display;

use askama::Template;

use crate::{GPL3_SDPX_IDENTIFIER, PRAGMA_GROTH16_VERIFIER};

pub mod encoding;

#[derive(Template, Default)]
#[template(path = "header_template.askama.sol", ext = "sol")]
pub(crate) struct HeaderInclusion<T: Template> {
    /// SPDX-License-Identifier
    pub sdpx: String,
    /// The `pragma` statement.
    pub pragma_version: String,
    /// The template to render alongside the header.
    pub template: T,
}

impl<T: Template> From<(String, String, T)> for HeaderInclusion<T> {
    fn from(value: (String, String, T)) -> Self {
        Self {
            sdpx: value.0,
            pragma_version: value.1,
            template: value.2,
        }
    }
}

impl<T: Template + Default> HeaderInclusion<T> {
    pub fn builder() -> HeaderInclusionBuilder<T> {
        HeaderInclusionBuilder::default()
    }
}

#[derive(Debug, Default)]
pub struct HeaderInclusionBuilder<T: Template + Default> {
    /// SPDX-License-Identifier
    sdpx: String,
    /// The `pragma` statement.
    pragma_version: String,
    /// The template to render alongside the header.
    template: T,
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

    pub fn template(mut self, template: T) -> Self {
        self.template = template;
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
