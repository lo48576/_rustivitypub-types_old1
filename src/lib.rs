//! Type definitions for rustivitypub.
#![warn(missing_docs)]

extern crate opaque_typedef;
#[macro_use]
extern crate opaque_typedef_macros;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;
extern crate url;

pub mod activitystreams;
pub mod base;
