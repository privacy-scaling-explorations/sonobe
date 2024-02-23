use askama::Template;

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
