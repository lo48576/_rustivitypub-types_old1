//! Fixed number time offset for Activity Streams 2.0.

use std::fmt;

use chrono;
use chrono::{FixedOffset, NaiveDate, NaiveDateTime};

use super::{As2TimeOffset, TimeOffsetError};


/// Fixed offset without seconds part.
///
/// This represents `time-numoffset` of
/// [RFC 3339](https://tools.ietf.org/html/rfc3339#section-5.6).
///
/// [`chrono::FixedOffset`] can treat second part (like `+23:59:58`), but it is
/// not allowed for Activity Streams 2.0 (and RFC 3339), because the syntax for
/// timezone is defined as `(Z|[+-]hh:mm)` (for real definition, see
/// <https://tools.ietf.org/html/rfc3339#section-5.6>).
///
/// Additionaly, in Activity Streams 2.0 (and RFC 3339), secfrac part is defined
/// as `1*DIGIT`, so it can take any number of digits.
/// However, [`chrono::DateTime`] can treat limited precisions of secfrac, so we
/// need dedicated types to treat it precisely.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct As2TimeNumOffset {
    /// Number of minutes to add to convert from UTC to the local time.
    minutes_local_minus_utc: i16,
}

impl As2TimeNumOffset {
    /// Creates a new positive `As2TimeNumOffset` (`+hh:mm`).
    pub fn new_positive(hour: u8, minute: u8) -> Result<Self, TimeOffsetError> {
        if hour >= 24 {
            Err(TimeOffsetError::InvalidHourPart(hour as i16))
        } else if minute >= 60 {
            Err(TimeOffsetError::InvalidMinutePart(minute))
        } else {
            Ok(Self {
                minutes_local_minus_utc: hour as i16 * 60 + minute as i16,
            })
        }
    }

    /// Creates a new negative `As2TimeNumOffset` (`-hh:mm`).
    ///
    /// Note that `As2TimeNumOffset` doesn't distinguish `-00:00` from `+00:00`.
    /// In other words, `As2TimeNumOffset::new_negative(0, 0)` is treated as
    /// `+00:00`.
    pub fn new_negative(hour: u8, minute: u8) -> Result<Self, TimeOffsetError> {
        if hour >= 24 {
            Err(TimeOffsetError::InvalidHourPart(-(hour as i16)))
        } else if minute >= 60 {
            Err(TimeOffsetError::InvalidMinutePart(minute))
        } else {
            Ok(Self {
                minutes_local_minus_utc: -(hour as i16 * 60 + minute as i16),
            })
        }
    }

    /// Creates a new `As2TimeNumOffset` from minutes offset.
    pub fn from_minutes(minutes_local_minus_utc: i16) -> Result<Self, TimeOffsetError> {
        if minutes_local_minus_utc >= 3600 || minutes_local_minus_utc <= -3600 {
            return Err(TimeOffsetError::MinutesOutOfRange(minutes_local_minus_utc));
        }
        Ok(Self {
            minutes_local_minus_utc,
        })
    }

    /// Creates a new `As2TimeNumOffset` from the given chrono offset.
    ///
    /// This will fail if the offset has seconds offset (i.e. unrepresentable
    /// with `[+-]hh:mm` format).
    // Can't implement as `TryFrom<T>` because `Self` itself implements
    // `chrono::Offset` and conflicts with reflexivity law.
    pub fn from_chrono_offset<T: chrono::Offset>(o: &T) -> Result<Self, TimeOffsetError> {
        let seconds = o.fix().local_minus_utc();
        let (min, sec_rem) = (seconds / 60, seconds % 60);
        if sec_rem != 0 {
            return Err(TimeOffsetError::NonZeroSecond);
        }
        if min > i16::max_value() as i32 {
            // Out of range.
            return Err(TimeOffsetError::MinutesOutOfRange(i16::max_value()));
        } else if min < i16::min_value() as i32 {
            // Out of range.
            return Err(TimeOffsetError::MinutesOutOfRange(i16::min_value()));
        }
        As2TimeNumOffset::from_minutes(min as i16)
    }

    /// Returns the number of minutes to add to convert from UTC to the local
    /// time.
    pub fn minutes_local_minus_utc(&self) -> i16 {
        self.minutes_local_minus_utc
    }
}

// For use with chrono.
impl fmt::Debug for As2TimeNumOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for As2TimeNumOffset {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (hour, minute) = (
            self.minutes_local_minus_utc / 60,
            self.minutes_local_minus_utc % 60,
        );
        write!(f, "{:+03}:{:02}", hour, minute.abs())
    }
}

impl ::std::str::FromStr for As2TimeNumOffset {
    type Err = TimeOffsetError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_timezone_offset(
            s.as_bytes(),
            || As2TimeNumOffset {
                minutes_local_minus_utc: 0,
            },
            |is_negative, hour, minute| {
                if is_negative {
                    As2TimeNumOffset::new_negative(hour, minute)
                } else {
                    As2TimeNumOffset::new_positive(hour, minute)
                }
            },
        )
    }
}

impl From<As2TimeOffset> for As2TimeNumOffset {
    fn from(o: As2TimeOffset) -> Self {
        o.num_offset()
    }
}

impl chrono::Offset for As2TimeNumOffset {
    fn fix(&self) -> FixedOffset {
        const MINUTES_TO_SECONDS: i32 = 60;
        FixedOffset::east(self.minutes_local_minus_utc as i32 * MINUTES_TO_SECONDS)
    }
}

impl chrono::TimeZone for As2TimeNumOffset {
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


/// Parses the timezone offset.
pub(super) fn parse_timezone_offset<T, Z, F>(
    bytes: &[u8],
    z: Z,
    hhmm: F,
) -> Result<T, TimeOffsetError>
where
    Z: FnOnce() -> T,
    // is_negative: bool, hour: u8, minute: u8
    F: FnOnce(bool, u8, u8) -> Result<T, TimeOffsetError>,
{
    let len = bytes.len();
    if len == 1 {
        if bytes[0] == b'Z' {
            return Ok(z());
        } else {
            return Err(TimeOffsetError::InvalidFormat);
        }
    } else if len == 6 {
        // 6: `"+hh:mm".len()`.
        let negative = match bytes[0] {
            b'+' => false,
            b'-' => true,
            _ => return Err(TimeOffsetError::InvalidFormat),
        };
        if bytes[3] != b':' {
            return Err(TimeOffsetError::InvalidFormat);
        }
        let hour1 = bytes[1];
        let hour2 = bytes[2];
        let minute1 = bytes[4];
        let minute2 = bytes[5];
        if !(hour1.is_ascii_digit() && hour2.is_ascii_digit() && minute1.is_ascii_digit()
            && minute2.is_ascii_digit())
        {
            return Err(TimeOffsetError::InvalidFormat);
        }
        let hour: u8 = (hour1 - b'0') * 10 + (hour2 - b'0');
        let minute: u8 = (minute1 - b'0') * 10 + (minute2 - b'0');
        return hhmm(negative, hour, minute);
    } else {
        return Err(TimeOffsetError::InvalidFormat);
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
    fn new() {
        fn ensure(is_negative: bool, hour: i16, minutes: i16, s: &str) {
            let min_abs = hour * 60 + minutes;
            let (offset_minutes, offset) = if is_negative {
                (
                    -min_abs,
                    As2TimeNumOffset::new_negative(hour as u8, minutes as u8),
                )
            } else {
                (
                    min_abs,
                    As2TimeNumOffset::new_positive(hour as u8, minutes as u8),
                )
            };
            let offset = offset.expect("Should never fail");
            assert_eq!(offset.minutes_local_minus_utc(), offset_minutes);
            assert_eq!(offset.to_string(), s);
            let offset2 =
                As2TimeNumOffset::from_minutes(offset_minutes).expect("Should never fail");
            assert_eq!(offset, offset2);
        }

        ensure(false, 0, 0, ZERO.0);
        ensure(false, 9, 10, POSITIVE.0);
        ensure(true, 18, 45, NEGATIVE.0);
    }

    #[test]
    fn display() {
        fn ensure((s, min): (&str, i16)) {
            let offset = As2TimeNumOffset::from_minutes(min).expect("Should never fail");
            assert_eq!(offset.to_string(), s);
        }

        ensure(ZERO);
        ensure(POSITIVE);
        ensure(NEGATIVE);
    }

    #[test]
    fn from_str() {
        fn ensure((s, min): (&str, i16)) {
            let offset: As2TimeNumOffset = s.parse().expect("Should never fail");
            assert_eq!(offset.minutes_local_minus_utc(), min);
        }

        ensure(Z);
        ensure(ZERO);
        ensure(UNKNOWN_LOCAL);
        ensure(POSITIVE);
        ensure(NEGATIVE);
    }
}
