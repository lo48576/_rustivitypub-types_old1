//! Time offset for Activity Streams 2.0.

use std::fmt;

use chrono;
use chrono::{FixedOffset, NaiveDate, NaiveDateTime};

use super::parse_timezone_offset;
use super::{As2TimeNumOffset, TimeOffsetError};


/// Time offset.
///
/// This represents `time-offset` of
/// [RFC 3339](https://tools.ietf.org/html/rfc3339#section-5.6).
///
/// Note that the offset is not allowed to have seconds (like `+hh:mm:ss`),
/// because the syntax is defined as
/// `"Z" / (("+" / "-") time-hour ":" time-minute)`, so
/// [`chrono::TimeNumOffset`] with seconds offset should never be used.
///
/// See <https://tools.ietf.org/html/rfc3339#section-5.6> (`time-offset`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum As2TimeOffset {
    /// `Z` timezone.
    Z,
    /// `[+-]hh:mm` offset (except for `-00:00`).
    KnownLocal(As2TimeNumOffset),
    /// `-00:00` offset.
    ///
    /// This has special meaning, so this is semantically different from `Z`
    /// and `+00:00`.
    ///
    /// See <https://tools.ietf.org/html/rfc3339#section-4.3> for detail.
    UnknownLocal,
}

impl As2TimeOffset {
    /// Creates a new `As2TimeOffset` with `KnownLocal` variant from the given
    /// chrono offset.
    ///
    /// This will fail if the offset has seconds offset (i.e. unrepresentable
    /// with `[+-]hh:mm` format).
    pub fn from_chrono_offset_known_local<T: chrono::Offset>(
        o: &T,
    ) -> Result<Self, TimeOffsetError> {
        As2TimeNumOffset::from_chrono_offset(o).map(As2TimeOffset::KnownLocal)
    }

    /// Creates a new `As2TimeOffset` from the given chrono offset.
    ///
    /// This will return `Ok(As2TimeOffset::Z)` if the offset is `+00:00`.
    ///
    /// This will fail if the offset has seconds offset (i.e. unrepresentable
    /// with `[+-]hh:mm` format).
    pub fn from_chrono_offset_known_or_z<T: chrono::Offset>(
        o: &T,
    ) -> Result<Self, TimeOffsetError> {
        if o.fix().local_minus_utc() == 0 {
            Ok(As2TimeOffset::Z)
        } else {
            As2TimeNumOffset::from_chrono_offset(o).map(As2TimeOffset::KnownLocal)
        }
    }

    /// Returns local num offset of the data.
    ///
    /// Note that `-00:00` has special meaning.
    /// See <https://tools.ietf.org/html/rfc3339#section-4.3> for detail.
    pub fn local_num_offset(&self) -> Option<As2TimeNumOffset> {
        match *self {
            As2TimeOffset::Z => Some(
                As2TimeNumOffset::new_positive(0, 0)
                    .unwrap_or_else(|_| unreachable!("Should never fail")),
            ),
            As2TimeOffset::KnownLocal(offset) => Some(offset),
            As2TimeOffset::UnknownLocal => None,
        }
    }

    /// Returns the num offset.
    pub fn num_offset(&self) -> As2TimeNumOffset {
        match *self {
            As2TimeOffset::Z | As2TimeOffset::UnknownLocal => As2TimeNumOffset::new_positive(0, 0)
                .unwrap_or_else(|_| unreachable!("Should never fail")),
            As2TimeOffset::KnownLocal(offset) => offset,
        }
    }

    /// Returns the number of minutes to add to convert from UTC to the local
    /// time.
    pub fn minutes_local_minus_utc(&self) -> i16 {
        match *self {
            As2TimeOffset::Z | As2TimeOffset::UnknownLocal => 0,
            As2TimeOffset::KnownLocal(offset) => offset.minutes_local_minus_utc(),
        }
    }
}

impl fmt::Display for As2TimeOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            As2TimeOffset::Z => f.write_str("Z"),
            As2TimeOffset::KnownLocal(offset) => offset.fmt(f),
            As2TimeOffset::UnknownLocal => f.write_str("-00:00"),
        }
    }
}

impl ::std::str::FromStr for As2TimeOffset {
    type Err = TimeOffsetError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_timezone_offset(
            s.as_bytes(),
            || As2TimeOffset::Z,
            |is_negative, hour, minute| {
                let offset = if is_negative {
                    if hour == 0 && minute == 0 {
                        // `-00:00`.
                        return Ok(As2TimeOffset::UnknownLocal);
                    }
                    As2TimeNumOffset::new_negative(hour, minute)
                } else {
                    As2TimeNumOffset::new_positive(hour, minute)
                };
                offset.map(As2TimeOffset::KnownLocal)
            },
        )
    }
}

impl chrono::Offset for As2TimeOffset {
    fn fix(&self) -> FixedOffset {
        const MINUTES_TO_SECONDS: i32 = 60;
        FixedOffset::east(self.minutes_local_minus_utc() as i32 * MINUTES_TO_SECONDS)
    }
}

impl chrono::TimeZone for As2TimeOffset {
    type Offset = Self;

    fn from_offset(offset: &Self::Offset) -> Self {
        *offset
    }

    fn offset_from_local_date(&self, _local: &NaiveDate) -> chrono::LocalResult<Self::Offset> {
        chrono::LocalResult::Single(*self)
    }

    fn offset_from_local_datetime(
        &self,
        _local: &NaiveDateTime,
    ) -> chrono::LocalResult<Self::Offset> {
        chrono::LocalResult::Single(*self)
    }

    fn offset_from_utc_date(&self, _utc: &NaiveDate) -> Self::Offset {
        *self
    }

    fn offset_from_utc_datetime(&self, _utc: &NaiveDateTime) -> Self::Offset {
        *self
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    const Z: (&str, i16) = ("Z", 0);
    const ZERO: (&str, i16) = ("+00:00", 0);
    const UNKNOWN_LOCAL: (&str, i16) = ("-00:00", 0);
    const POSITIVE: (&str, i16) = ("+09:10", 9 * 60 + 10);
    const NEGATIVE: (&str, i16) = ("-18:45", -(18 * 60 + 45));

    #[test]
    fn display() {
        fn ensure((s, min): (&str, i16)) {
            let num_offset = As2TimeNumOffset::from_minutes(min).expect("Should never fail");
            let offset = As2TimeOffset::KnownLocal(num_offset);
            assert_eq!(offset.to_string(), s);
        }

        ensure(ZERO);
        ensure(POSITIVE);
        ensure(NEGATIVE);
        assert_eq!(As2TimeOffset::UnknownLocal.to_string(), "-00:00");
        assert_eq!(As2TimeOffset::Z.to_string(), "Z");
    }

    #[test]
    fn from_str() {
        fn ensure<O: Into<Option<As2TimeOffset>>>((s, min): (&str, i16), special: O) {
            let offset: As2TimeOffset = s.parse().expect("Should never fail");
            if let Some(special) = special.into() {
                assert_eq!(offset, special);
            }
            assert_eq!(offset.num_offset().minutes_local_minus_utc(), min);
        }

        ensure(Z, As2TimeOffset::Z);
        ensure(ZERO, None);
        ensure(UNKNOWN_LOCAL, As2TimeOffset::UnknownLocal);
        ensure(POSITIVE, None);
        ensure(NEGATIVE, None);
    }
}
