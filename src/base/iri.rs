//! IRI and URI types.

use opaque_typedef::{OpaqueTypedef, OpaqueTypedefUnsized};
pub use url::ParseError as UrlParseError;
pub use url::Url;


/// IRI and resolved URI.
// NOTE: For now, don't derive `{,Partial}{Eq,Ord}` and `Hash` because I'm not
// sure how they should be ordered or compared.
// If you should compare them, use raw IRI or resolved URI.
#[derive(Debug, Clone)]
pub struct Iri {
    /// Raw IRI string.
    raw: IriString,
    /// Resolved URL.
    resolved: Url,
}

impl Iri {
    /// Creates a new `Iri`.
    pub fn new<S: AsRef<str> + Into<String>>(s: S) -> Result<Self, UrlParseError> {
        let resolved = Url::parse(s.as_ref())?;
        let raw = IriString(s.into());
        Ok(Iri { raw, resolved })
    }

    /// Returns raw IRI string slice.
    pub fn raw(&self) -> &IriStr {
        self.raw.as_iri_str()
    }

    /// Returns reference to the resolved URI.
    pub fn resolved(&self) -> &Url {
        &self.resolved
    }

    /// Deconstructs `Iri` into `IriString` and `url::Url`.
    pub fn deconstruct(self) -> (IriString, Url) {
        (self.raw, self.resolved)
    }
}


/// Validates the given string as IRI.
///
/// This is intended to be used by `opaque_typedef`.
fn validate_iri_str<S: AsRef<str>>(s: S) -> Result<S, UrlParseError> {
    let _ = Url::parse(s.as_ref())?;
    Ok(s)
}


/// IRI string slice.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedefUnsized)]
#[repr(C)]
#[opaque_typedef(
    derive(
        AsRef(Deref, Self_),
        Deref,
        Display,
        Into(Arc, Box, Rc, Inner),
        PartialEq(Inner, InnerRev, InnerCow, SelfCow, SelfCowRev),
        PartialOrd(Inner, InnerRev, InnerCow, SelfCow, SelfCowRev)
    )
)]
#[opaque_typedef(
    validation(
        validator = "validate_iri_str",
        error_type = "UrlParseError",
        error_msg = "Failed to create `IriString`"
    )
)]
pub struct IriStr(str);

impl IriStr {
    /// Creates a new `IriStr`.
    ///
    /// If you want `url::Url`, you should use `Iri::new()`.
    pub fn new(s: &str) -> Result<&IriStr, UrlParseError> {
        Ok(IriStr::from_str_unchecked(validate_iri_str(s)?))
    }

    /// Creates `IriStr` from the string slice.
    ///
    /// This is intended to be used by `opaque_typedef`, and it is because this
    /// function is not `unsafe`.
    fn from_str_unchecked(s: &str) -> &Self {
        let iri = unsafe { <Self as OpaqueTypedefUnsized>::from_inner_unchecked(s) };
        // Validation requires parsing and it costs, so run this assert only
        // for debug build.
        debug_assert!(
            validate_iri_str(s).is_ok(),
            "Valid IRI string should be passed to `IriStr::from_str_unchecked()`, but got {:?}",
            s
        );
        iri
    }

    /// Creates an `Url`.
    ///
    /// If you want both `Iri` and `Url` at once, you should use `Iri::new`.
    pub fn to_uri(&self) -> Url {
        Url::parse(&self.0).unwrap_or_else(|e| {
            unreachable!(
                "`IriString` should have valid IRI string, but parsing failed: {}",
                e
            )
        })
    }
}

impl ToOwned for IriStr {
    type Owned = IriString;

    fn to_owned(&self) -> Self::Owned {
        unsafe { <IriString as OpaqueTypedef>::from_inner_unchecked(self.0.to_owned()) }
    }
}


/// Owned IRI string.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedef)]
#[opaque_typedef(
    derive(
        AsRef(Deref, Inner),
        Deref,
        Display,
        IntoInner,
        PartialEq(Inner, InnerRev),
        PartialOrd(Inner, InnerRev)
    )
)]
#[opaque_typedef(deref(target = "IriStr", deref = "IriStr::from_str_unchecked"))]
#[opaque_typedef(
    validation(
        validator = "validate_iri_str",
        error_type = "UrlParseError",
        error_msg = "Failed to create `IriString`"
    )
)]
pub struct IriString(String);

impl IriString {
    /// Creates a new `IriString`.
    ///
    /// If you want `url::Url`, you should use `Iri::new()`.
    pub fn new(s: String) -> Result<IriString, UrlParseError> {
        Ok(IriString(validate_iri_str(s)?))
    }

    /// Returns `&IriStr` slice for the inner IRI string.
    pub fn as_iri_str(&self) -> &IriStr {
        unsafe { <IriStr as OpaqueTypedefUnsized>::from_inner_unchecked(self.0.as_str()) }
    }

    /// Creates an `Url`.
    ///
    /// If you want both `IriString` and `Url` at once, you should use
    /// `Iri::new`.
    pub fn to_uri(&self) -> Url {
        Url::parse(&self.0).unwrap_or_else(|e| {
            unreachable!(
                "`IriString` should have valid IRI string, but parsing failed: {}",
                e
            )
        })
    }
}

impl ::std::borrow::Borrow<IriStr> for IriString {
    fn borrow(&self) -> &IriStr {
        unsafe { <IriStr as OpaqueTypedefUnsized>::from_inner_unchecked(&self.0) }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    fn ensure_ok(s: &str) {
        let iri = Iri::new(s).unwrap();
        let iri_str = IriStr::new(s).unwrap();
        let iri_string = IriString::new(s.to_owned()).unwrap();
        // Compare URLs.
        assert_eq!(s, iri.raw());
        assert_eq!(iri.resolved(), &Url::parse(iri.raw()).unwrap());
        // Compare `IriStr`s.
        assert_eq!(iri_string.as_iri_str(), iri_str);
        assert_eq!(iri_string.as_iri_str().to_owned(), iri_string);
    }

    #[test]
    fn ok_cases() {
        let ok_cases = [
            "https://example.com/",
            "https://example.com/テスト",
            "https://example.com/%e3%83%86ス%E3%83%88",
            "https://テスト.日本語/%E3%83%86%E3%82%B9%E3%83%88",
        ];
        ok_cases.into_iter().for_each(|&s| ensure_ok(s));
    }
}
