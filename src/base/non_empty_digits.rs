//! Digits string types and functions.

use std::error;
use std::fmt;

use opaque_typedef;


/// A string slice consists of one or more decimal digits.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, OpaqueTypedefUnsized)]
#[repr(C)]
#[opaque_typedef(
    derive(
        AsRef(Deref, Self_),
        Deref,
        Display,
        Into(Arc, Box, Rc, Inner),
        PartialEq(Inner, InnerRev, InnerCow, InnerCowRev, SelfCow, SelfCowRev),
        PartialOrd(Inner, InnerRev, InnerCow, InnerCowRev, SelfCow, SelfCowRev)
    )
)]
#[opaque_typedef(
    validation(
        validator = "ensure_one_or_more_digits",
        error_type = "DigitsError",
        error_msg = "Failed to create `NonEmptyDigitsStr`"
    )
)]
pub struct NonEmptyDigitsStr(str);

impl NonEmptyDigitsStr {
    /// Creates a new `NonEmptyDigitsStr` from the given string.
    pub fn new(s: &str) -> Result<&Self, DigitsError> {
        opaque_typedef::OpaqueTypedefUnsized::try_from_inner(s.as_ref())
    }

    /// Creates a new `NonEmptyDigitsStr` from the given bytes slice.
    pub fn from_bytes(s: &[u8]) -> Result<&Self, DigitsError> {
        let s = ensure_one_or_more_digits(s)?;
        let s = unsafe {
            // This is safe because `s` contains only ASCII digits.
            let s = ::std::str::from_utf8_unchecked(s);
            // This is also safe because the validation has already been
            // done.
            opaque_typedef::OpaqueTypedefUnsized::from_inner_unchecked(s)
        };
        Ok(s)
    }

    /// Creates a new `NonEmptyDigitsStr` from the given bytes slice without
    /// checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it are all digits. If this constraint is violated, undefined
    /// behavior results, as the rest of Rust assumes that `&NonEmptyDigitsStr`
    /// is not empty and only contains digits.
    ///
    /// So, the argument should fulfill:
    ///
    /// * The slice is not empty, and
    /// * The slice contains only ASCII digits.
    pub unsafe fn from_bytes_unchecked(s: &[u8]) -> &Self {
        let s = ::std::str::from_utf8_unchecked(s);
        opaque_typedef::OpaqueTypedefUnsized::from_inner_unchecked(s)
    }

    /// Returns a reference to the inner string silce.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Parses the string as `u64`.
    ///
    /// Returns `None` iff overflow happened.
    pub fn parse_u64(&self) -> Option<u64> {
        self.0.parse().ok()
    }

    /// Parses the string as `usize`.
    ///
    /// Returns `None` iff overflow happened.
    pub fn parse_usize(&self) -> Option<usize> {
        self.0.parse().ok()
    }

    /// Returns a character (an ASCII byte) at the given index if available.
    ///
    /// Returns `None` iff the index is out of range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("5678901234").expect("Should never fail");
    /// assert_eq!(s.char_at(2), Some('7'));
    /// assert_eq!(s.char_at(99), None);
    /// ```
    pub fn char_at(&self, idx: usize) -> Option<char> {
        self.as_bytes().get(idx).map(|&b| b as char)
    }

    /// Returns a digit value (0--9 integer) at the given index if available.
    ///
    /// Returns `None` iff the index is out of range.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("5678901234").expect("Should never fail");
    /// assert_eq!(s.digit_at(2), Some(7));
    /// assert_eq!(s.digit_at(99), None);
    /// ```
    pub fn digit_at(&self, idx: usize) -> Option<u8> {
        self.as_bytes().get(idx).map(|&b| b - b'0')
    }

    /// Returns the substring (slice).
    ///
    /// Returns `None` iff the result slice is empty (i.e. `begin == end`).
    ///
    /// # Panics
    ///
    /// Panics if the indices is out of range, or range is invalid.
    /// In other words, `begin.unwrap_or(0) <= end.unwrap_or(len) &&
    /// end.unwrap_or(len) <= len` should hold.
    pub fn substring<B, E>(&self, begin: B, end: E) -> Option<&Self>
    where
        B: Into<Option<usize>>,
        E: Into<Option<usize>>,
    {
        let bytes = self.as_bytes();
        let slice = match (begin.into(), end.into()) {
            (None, None) => return Some(self),
            (None, Some(end)) => &bytes[..end],
            (Some(begin), None) => &bytes[begin..],
            (Some(begin), Some(end)) => &bytes[begin..end],
        };
        if slice.is_empty() {
            None
        } else {
            let slice = unsafe {
                // This is safe because:
                //
                //  * the slice is not empty, and
                //  * the slice contains only ASCII digits.
                Self::from_bytes_unchecked(slice)
            };
            Some(slice)
        }
    }

    /// Returns the left substring as possible.
    ///
    /// Returns `None` iff the result string is empty (i.e. `take_max == 0`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("0123456789").expect("Should never fail");
    /// assert_eq!(s.left_substring(0), None);
    /// assert_eq!(s.left_substring(5).map(|s| s.as_str()), Some("01234"));
    /// assert_eq!(s.left_substring(99).map(|s| s.as_str()), Some("0123456789"));
    /// ```
    pub fn left_substring(&self, take_max: usize) -> Option<&NonEmptyDigitsStr> {
        self.substring(None, take_max.min(self.len()))
    }

    /// Returns the right substring as possible.
    ///
    /// Returns `None` iff the result string is empty (i.e. `take_max == 0`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("0123456789").expect("Should never fail");
    /// assert_eq!(s.right_substring(0), None);
    /// assert_eq!(s.right_substring(5).map(|s| s.as_str()), Some("56789"));
    /// assert_eq!(s.right_substring(99).map(|s| s.as_str()), Some("0123456789"));
    /// ```
    pub fn right_substring(&self, take_max: usize) -> Option<&NonEmptyDigitsStr> {
        let len = self.len();
        self.substring(len - take_max.min(len), None)
    }

    /// Trims the leading zeros.
    ///
    /// Returns `None` iff all digits are zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("00420").expect("Should never fail");
    /// assert_eq!(s.trim_leading_zeros().map(|v| v.as_str()), Some("420"));
    ///
    /// let s = NonEmptyDigitsStr::new("0000").expect("Should never fail");
    /// assert_eq!(s.trim_leading_zeros(), None);
    /// ```
    pub fn trim_leading_zeros(&self) -> Option<&NonEmptyDigitsStr> {
        let bytes = self.as_bytes();
        let nonzero_pos = bytes.into_iter().position(|&v| v != b'0')?;
        self.substring(nonzero_pos, None)
    }

    /// Trims the trailing zeros.
    ///
    /// Returns `None` iff all digits are zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("04200").expect("Should never fail");
    /// assert_eq!(s.trim_trailing_zeros().map(|v| v.as_str()), Some("042"));
    ///
    /// let s = NonEmptyDigitsStr::new("0000").expect("Should never fail");
    /// assert_eq!(s.trim_trailing_zeros(), None);
    /// ```
    pub fn trim_trailing_zeros(&self) -> Option<&NonEmptyDigitsStr> {
        let bytes = self.as_bytes();
        let nonzero_pos = bytes.into_iter().rposition(|&v| v != b'0')?;
        assert!(nonzero_pos < bytes.len());
        self.substring(None, nonzero_pos + 1)
    }

    /// Parses the slice as left aligned digits with the given width.
    ///
    /// If the string is shorter than the given width, it is treated as
    /// zero-padded.
    ///
    /// Returns `None` if the given width is 0 or overflow happened.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustivitypub_types::base::NonEmptyDigitsStr;
    /// let s = NonEmptyDigitsStr::new("01234").expect("Should never fail");
    /// assert_eq!(s.parse_u64_left_aligned_substring(0), None);
    /// assert_eq!(s.parse_u64_left_aligned_substring(2), Some(1));
    /// assert_eq!(s.parse_u64_left_aligned_substring(5), Some(1234));
    /// assert_eq!(s.parse_u64_left_aligned_substring(8), Some(1234000));
    ///
    /// let s = NonEmptyDigitsStr::new("9").expect("Should never fail");
    /// assert_eq!(s.parse_u64_left_aligned_substring(99), None);
    /// ```
    pub fn parse_u64_left_aligned_substring(&self, width: usize) -> Option<u64> {
        let (width, slice) = {
            let substr = self.left_substring(width)?;
            let slice = match substr.trim_leading_zeros() {
                Some(s) => s,
                None => return Some(0),
            };
            let trimmed_len = substr.len() - slice.len();
            (width - trimmed_len, slice)
        };

        // 2^64 = 18446744073709551616 (20 digits).
        const MAX_DIGITS: usize = 20;
        if width > MAX_DIGITS {
            // Overflows absolutely.
            return None;
        }
        let slice_len = slice.len();
        let mut buf = [b'0'; MAX_DIGITS];
        // This condition holds because `buf.len() == MAX_DIGITS &&
        // MAX_DIGITS >= width && width >= substr && substr >= slice`.
        assert!(buf.len() >= slice_len);
        buf[..slice_len].copy_from_slice(slice.as_bytes());

        // This condition holds because if `width == 0`,
        // `self.left_substring(width)` returns `None` and execution does not
        // reach here.
        assert!(width > 0);
        let s = unsafe {
            // This is safe because:
            //
            //  * `buf` is not empty and `width > 0`, and
            //  * `buf` contains only ASCII digits.
            Self::from_bytes_unchecked(&buf[..width])
        };
        s.parse_u64()
    }
}

impl ToOwned for NonEmptyDigitsStr {
    type Owned = NonEmptyDigitsString;

    fn to_owned(&self) -> Self::Owned {
        NonEmptyDigitsString::new(self.as_str().to_owned())
            .unwrap_or_else(|e| unreachable!("Should never fail: {}", e))
    }
}


/// A string consists of one or more decimal digits.
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
#[opaque_typedef(
    deref(target = "NonEmptyDigitsStr", deref = "(|s| NonEmptyDigitsStr::new(s).unwrap())")
)]
#[opaque_typedef(
    validation(
        validator = "ensure_one_or_more_digits",
        error_type = "DigitsError",
        error_msg = "Failed to create `NonEmptyDigitsString`"
    )
)]
pub struct NonEmptyDigitsString(String);

impl NonEmptyDigitsString {
    /// Creates a new `NonEmptyDigitsString` from the given string.
    pub fn new<S: Into<String>>(s: S) -> Result<Self, DigitsError> {
        opaque_typedef::OpaqueTypedef::try_from_inner(s.into())
    }

    /// Creates a new `NonEmptyDigitsString` from the given bytes.
    pub fn from_bytes<S: Into<Vec<u8>>>(s: S) -> Result<Self, DigitsError> {
        let bytes = ensure_one_or_more_digits(s.into())?;
        let v = unsafe {
            // This is safe because `s` contains only ASCII digits.
            let s = String::from_utf8_unchecked(bytes);
            // This is also safe because the validation has already been
            // done.
            opaque_typedef::OpaqueTypedef::from_inner_unchecked(s)
        };
        Ok(v)
    }

    /// Creates a new `NonEmptyDigitsString` from the given string without
    /// checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it are all digits. If this constraint is violated, undefined
    /// behavior results, as the rest of Rust assumes that
    /// `NonEmptyDigitsString` is not empty and only contains digits.
    ///
    /// So, the argument should fulfill:
    ///
    /// * The string is not empty, and
    /// * The string contains only ASCII digits.
    pub unsafe fn new_unchecked(s: String) -> Self {
        opaque_typedef::OpaqueTypedef::from_inner_unchecked(s)
    }

    /// Creates a new `NonEmptyDigitsString` from the given bytes without
    /// checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the string passed
    /// to it are all digits. If this constraint is violated, undefined
    /// behavior results, as the rest of Rust assumes that
    /// `NonEmptyDigitsString` is not empty and only contains digits.
    ///
    /// So, the argument should fulfill:
    ///
    /// * The vector is not empty, and
    /// * The vector contains only ASCII digits.
    pub unsafe fn from_bytes_unchecked(v: Vec<u8>) -> Self {
        Self::new_unchecked(String::from_utf8_unchecked(v))
    }

    /// Returns a reference to the inner string silce.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Creates a new `NonEmptyDigitsString` from the given integer value.
    pub fn from_u64(&self, value: u64) -> Self {
        let s = value.to_string();
        unsafe {
            // This is safe because:
            //
            //  * `s` is not empty, and
            //  * `s` contains only ASCII digits.
            Self::new_unchecked(s)
        }
    }

    /// Creates a new `NonEmptyDigitsString` from the given integer value.
    pub fn from_usize(&self, value: usize) -> Self {
        let s = value.to_string();
        unsafe {
            // This is safe because:
            //
            //  * `s` is not empty, and
            //  * `s` contains only ASCII digits.
            Self::new_unchecked(s)
        }
    }
}

impl AsRef<str> for NonEmptyDigitsString {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for NonEmptyDigitsString {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_ref()
    }
}

impl ::std::borrow::Borrow<NonEmptyDigitsStr> for NonEmptyDigitsString {
    fn borrow(&self) -> &NonEmptyDigitsStr {
        // `AsRef<NonEmptyDigitsStr> for NonEmptyDigitsString` is automatically
        // implemented by `opaque_typedef`.
        self.as_ref()
    }
}


/// A type for digits string creation error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DigitsError {
    /// String is empty.
    Empty,
    /// String has non-digit character.
    NonDigit,
}

impl error::Error for DigitsError {
    fn description(&self) -> &str {
        match *self {
            DigitsError::Empty => "Got an empty string, but the string should never be empty",
            DigitsError::NonDigit => {
                "String should have only digits, but found a non-digit character"
            },
        }
    }
}

impl fmt::Display for DigitsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::error::Error;

        write!(f, "{}", self.description())
    }
}


/// Checks whether the given string consists of decimal digits.
fn ensure_one_or_more_digits<S: AsRef<[u8]>>(s: S) -> Result<S, DigitsError> {
    {
        let s = s.as_ref();
        if s.len() == 0 {
            return Err(DigitsError::Empty);
        } else if !s.into_iter().all(|v| v.is_ascii_digit()) {
            return Err(DigitsError::NonDigit);
        }
    }
    Ok(s)
}


#[cfg(test)]
mod tests {
    use super::*;

    const OK: &[&str] = &["0", "000", "123", "0999"];
    const EMPTY: &str = "";
    const NON_DIGIT: &[&str] = &["123d", "a123", "8bad8", " 1", "0 ", "0.0"];

    #[test]
    fn test_validator() {
        OK.iter().for_each(|&s| {
            assert_eq!(ensure_one_or_more_digits(s), Ok(s));
        });
        assert_eq!(ensure_one_or_more_digits(EMPTY), Err(DigitsError::Empty));
        NON_DIGIT.iter().for_each(|&s| {
            assert_eq!(ensure_one_or_more_digits(s), Err(DigitsError::NonDigit));
        });
    }

    mod slice {
        use super::*;

        #[test]
        fn test_slice() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsStr::new(s);
                assert_eq!(digits.map(|v| v.as_str()), Ok(s));
            });
            assert_eq!(NonEmptyDigitsStr::new(EMPTY), Err(DigitsError::Empty));
            NON_DIGIT.iter().for_each(|&s| {
                assert_eq!(NonEmptyDigitsStr::new(s), Err(DigitsError::NonDigit));
            });
        }

        #[test]
        fn display_slice() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsStr::new(s).unwrap();
                assert_eq!(digits.to_string(), s);
            });
        }

        #[test]
        fn len_owned() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsStr::new(s).unwrap();
                assert_eq!(digits.len(), s.len());
            });
        }

        #[test]
        fn as_ref_str() {
            let digits = NonEmptyDigitsStr::new(OK[0]).unwrap();
            let _: &str = digits.as_str();
            let _: &str = digits.as_ref();
            let _: &NonEmptyDigitsStr = digits.as_ref();
        }

        #[test]
        fn deref() {
            let digits = NonEmptyDigitsStr::new(OK[0]).unwrap();
            let _: &str = &digits;
        }
    }

    mod owned {
        use super::*;

        #[test]
        fn test_owned() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsString::new(s.to_owned());
                assert_eq!(digits.as_ref().map(|v| v.as_str()), Ok(s));
            });
            assert_eq!(
                NonEmptyDigitsString::new(EMPTY.to_owned()),
                Err(DigitsError::Empty)
            );
            NON_DIGIT.iter().for_each(|&s| {
                assert_eq!(
                    NonEmptyDigitsString::new(s.to_owned()),
                    Err(DigitsError::NonDigit)
                );
            });
        }

        #[test]
        fn display_owned() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsString::new(s.to_owned()).unwrap();
                assert_eq!(digits.to_string(), s);
            });
        }

        #[test]
        fn len_owned() {
            OK.iter().for_each(|&s| {
                let digits = NonEmptyDigitsString::new(s).unwrap();
                assert_eq!(digits.len(), s.len());
            });
        }

        #[test]
        fn as_ref_str() {
            let digits = NonEmptyDigitsString::new(OK[0].to_owned()).unwrap();
            let _: &str = digits.as_str();
            let _: &str = digits.as_ref();
            let _: &String = digits.as_ref();
            let _: &NonEmptyDigitsStr = digits.as_ref();
        }

        #[test]
        fn deref() {
            let digits = NonEmptyDigitsString::new(OK[0].to_owned()).unwrap();
            let _: &str = &digits;
            let _: &NonEmptyDigitsStr = &digits;
        }
    }
}
