//! Minimal JSON-LD features required for ActivityStreams.
//!
//! See <https://www.w3.org/TR/2014/REC-json-ld-20140116/>.

use serde_json::Value;

use activitystreams::core::consts;


/// `@context`.
///
/// See <https://www.w3.org/TR/2014/REC-json-ld-20140116/#the-context>.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Context(Value);

impl Context {
    /// Default vocabulary (might be explicitly specified by `@vocab`).
    ///
    /// Note that this may return a compact IRI, so the return type is not
    /// `&Iri` but `&str`.
    ///
    /// Also not that this function doesn't any modification to the value (i.e.
    /// if the context has `@base` or something, this function doesn't interpret
    /// them at all and will return raw `@vocab` value).
    ///
    /// See <https://www.w3.org/TR/2014/REC-json-ld-20140116/#default-vocabulary>.
    fn default_vocab(&self) -> Option<&str> {
        match self.0 {
            Value::Null | Value::Bool(_) | Value::Number(_) => None,
            Value::String(ref s) => Some(s),
            Value::Array(ref values) => values.get(0).and_then(|v| v.as_str()),
            Value::Object(ref map) => map.get("@vocab").and_then(|v| v.as_str()),
        }
    }

    /// Checks whether the `@context` value has Activity Streams context.
    ///
    /// See <https://www.w3.org/TR/2017/REC-activitystreams-core-20170523/#jsonld>.
    pub fn has_activity_streams_context(&self) -> bool {
        self.default_vocab().map_or(false, |v| {
            v == consts::JSON_LD_CONTEXT_HTTPS || v == consts::JSON_LD_CONTEXT_HTTP
        })
    }
}
