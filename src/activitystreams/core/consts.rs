//! Activity Streams core constants.


/// MIME type for Activity Streams Documents.
///
/// See <https://www.w3.org/TR/2017/REC-activitystreams-core-20170523/#syntaxconventions>.
pub const DOCUMENT_MIME_TYPE: &str = "application/activity+json";

/// JSON-LD `@context` value for Activity Streams 2.0 documents.
///
/// See <https://www.w3.org/TR/2017/REC-activitystreams-core-20170523/#jsonld>.
pub const JSON_LD_CONTEXT_HTTPS: &str = "https://www.w3.org/ns/activitystreams";

/// JSON-LD alternative `@context` value for Activity Streams 2.0 documents.
///
/// See <https://www.w3.org/TR/2017/REC-activitystreams-core-20170523/#jsonld>.
pub const JSON_LD_CONTEXT_HTTP: &str = "http://www.w3.org/ns/activitystreams";
