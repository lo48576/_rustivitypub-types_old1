//! Datetime for Activity Streams 2.0.
//!
//! See [RFC 3339](https://tools.ietf.org/html/rfc3339) and [Activity Stream 2.0
//! spec](https://www.w3.org/TR/2017/REC-activitystreams-core-20170523/#dates)
//! for detail.

use std::convert::TryFrom;
use std::fmt;

use chrono;
use chrono::{DateTime, NaiveDateTime};

use base::NonEmptyDigitsString;

pub use self::error::{DateTimeCreationError, TimeOffsetError};
use self::time_num_offset::parse_timezone_offset;
pub use self::time_num_offset::As2TimeNumOffset;
pub use self::time_offset::As2TimeOffset;

pub mod error;
pub mod time_num_offset;
pub mod time_offset;


/// Datetime for Activity Streams 2.0.
///
/// This type can represent omitted second or arbitrary precision of secfrac.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct As2DateTime {
    /// Datetime with time offset info.
    ///
    /// Second part should be zero if `is_second_omitted` is `true`.
    ///
    /// Subsecond should be consistent with `secfrac` field.
    datetime: DateTime<As2TimeOffset>,
    /// Whether the `[":" time-second]` part is omitted.
    is_second_omitted: bool,
    /// `[time-secfrac]` part.
    secfrac: Option<NonEmptyDigitsString>,
}

impl As2DateTime {
    /// Creates a new `As2DateTime`.
    ///
    /// If subsecond of `datetime` and `secfrac` differs, `secfrac` will be
    /// used.
    pub fn new(
        datetime: DateTime<As2TimeOffset>,
        omit_second: bool,
        secfrac: Option<NonEmptyDigitsString>,
    ) -> Self {
        use chrono::Timelike;

        const NANOSEC_WIDTH: usize = 9;
        let nanosec = secfrac
            .as_ref()
            .and_then(|num| num.parse_u64_left_aligned_substring(NANOSEC_WIDTH))
            .unwrap_or(0) as u32;
        let second = if omit_second { 0 } else { datetime.second() };
        let datetime =
            datetime
                .date()
                .and_hms_nano(datetime.hour(), datetime.minute(), second, nanosec);
        Self {
            datetime,
            is_second_omitted: omit_second,
            secfrac,
        }
    }

    /// Creates a new `As2DateTime`.
    ///
    /// # Panics
    ///
    /// Panics if `nanosecond` value is more than 1 seconds (i.e. the value is
    /// larger than `1_000_000_000`.
    pub fn with_nanosecond(
        datetime: DateTime<As2TimeOffset>,
        omit_second: bool,
        nanosecond: u32,
    ) -> Self {
        const NANOSECOND_PER_SECOND: u32 = 1_000_000_000;
        assert!(
            nanosecond < NANOSECOND_PER_SECOND,
            "`nanosecond` value (`{}`) should be less than 1s (`{}`)",
            nanosecond,
            NANOSECOND_PER_SECOND
        );

        let secfrac = NonEmptyDigitsString::new(format!("{:09}", nanosecond))
            .unwrap_or_else(|e| unreachable!("Should never fail: {}", e));
        Self::new(datetime, omit_second, Some(secfrac))
    }

    /// Creates a new `As2DateTime` from the given `chrono::DateTime`.
    pub fn from_chrono_as2_datetime_with_as2_time_offset(
        datetime: DateTime<As2TimeOffset>,
        omit_second: bool,
        omit_nanosecond: bool,
    ) -> Self {
        use chrono::Timelike;

        let nanosec = datetime.nanosecond();
        let secfrac = if omit_nanosecond {
            None
        } else {
            // `chrono::DateTime` has nanosecond precision.
            Some(
                NonEmptyDigitsString::new(format!("{:09}", nanosec))
                    .unwrap_or_else(|e| unreachable!("Should never fail: {}", e)),
            )
        };
        let second = if omit_second { 0 } else { datetime.second() };
        let datetime =
            datetime
                .date()
                .and_hms_nano(datetime.hour(), datetime.minute(), second, nanosec);
        Self {
            datetime,
            is_second_omitted: omit_second,
            secfrac,
        }
    }

    /// Creates a new `As2DateTime` from the given `chrono::DateTime`.
    pub fn from_chrono_datetime<Tz: chrono::TimeZone>(
        datetime: DateTime<Tz>,
        omit_second: bool,
        omit_nanosecond: bool,
    ) -> Result<Self, TimeOffsetError> {
        let offset = As2TimeOffset::from_chrono_offset_known_local(datetime.offset())?;
        let datetime = datetime.with_timezone(&offset);
        Ok(Self::from_chrono_as2_datetime_with_as2_time_offset(
            datetime,
            omit_second,
            omit_nanosecond,
        ))
    }

    /// Returns a reference to the inner `chrono::DateTime<As2TimeOffset>`.
    pub fn chrono_datetime(&self) -> &DateTime<As2TimeOffset> {
        &self.datetime
    }

    /// Returns a reference to the inner `As2TimeOffset`.
    pub fn offset(&self) -> &As2TimeOffset {
        self.datetime.offset()
    }
}

impl fmt::Display for As2DateTime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use chrono::format::strftime::StrftimeItems;

        let format = if self.is_second_omitted {
            StrftimeItems::new("%FT%H:%M")
        } else {
            StrftimeItems::new("%FT%T")
        };
        write!(
            f,
            "{}",
            self.datetime.naive_local().format_with_items(format)
        )?;
        if let Some(ref secfrac) = self.secfrac {
            write!(f, ".{}", secfrac)?;
        }
        write!(f, "{}", self.datetime.offset())
    }
}

impl ::std::str::FromStr for As2DateTime {
    type Err = DateTimeCreationError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use chrono::TimeZone;

        // format: `YYYY-MM-DDThh:mm[:ss][.secfrac](Z|[+-]hh:mm)`
        // datetime_part: `YYYY-MM-DDThh:mm[:ss][.secfrac]`
        // tz_part: `Z|[+-]hh:mm`
        // ymdhms_part: `YYYY-MM-DDThh:mm[:ss]`
        // secfrac_part: `[.secfrac]`
        let (datetime_part, tz_part) = {
            let tz_begin = s.rfind(|c| c == 'Z' || c == '+' || c == '-')
                .ok_or(DateTimeCreationError::NoTimeZone)?;
            s.split_at(tz_begin)
        };
        let (ymdhms_part, secfrac_part) = {
            match datetime_part.find('.') {
                Some(pos) => {
                    let (ymdhms, secfrac) = datetime_part.split_at(pos);
                    (ymdhms, &secfrac[1..])
                },
                None => (datetime_part, ""),
            }
        };

        let (local_datetime, is_second_omitted) = {
            const FORMAT_FULL: &str = "%FT%T";
            const FORMAT_WITHOUT_SECOND: &str = "%FT%H:%M";
            NaiveDateTime::parse_from_str(ymdhms_part, FORMAT_FULL)
                .map(|v| (v, false))
                .or_else(|_| {
                    NaiveDateTime::parse_from_str(ymdhms_part, FORMAT_WITHOUT_SECOND)
                        .map(|v| (v, true))
                })
                .map_err(|_| DateTimeCreationError::InvalidFormat)?
        };
        let secfrac = if secfrac_part.is_empty() {
            None
        } else {
            Some(NonEmptyDigitsString::new(secfrac_part.to_owned())
                .map_err(|_| DateTimeCreationError::InvalidFormat)?)
        };
        let offset = tz_part
            .parse::<As2TimeOffset>()
            .map_err(DateTimeCreationError::Offset)?;
        let datetime = offset
            .from_local_datetime(&local_datetime)
            .single()
            .unwrap_or_else(|| unreachable!("Should never fail"));
        Ok(Self::new(datetime, is_second_omitted, secfrac))
    }
}

impl From<As2DateTime> for DateTime<As2TimeNumOffset> {
    fn from(o: As2DateTime) -> Self {
        use chrono::TimeZone;

        o.offset()
            .num_offset()
            .from_utc_datetime(&o.datetime.naive_utc())
    }
}

impl<Tz: chrono::TimeZone> TryFrom<DateTime<Tz>> for As2DateTime {
    type Error = TimeOffsetError;

    fn try_from(source: DateTime<Tz>) -> Result<Self, Self::Error> {
        Self::from_chrono_datetime(source, false, false)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    mod raw_datetime {
        use chrono::NaiveDate;

        use super::*;

        fn test_for_cases<F>(for_case: F)
        where
            // datetime_str: &str,
            // naive_date: NaiveDate,
            // (hour, minute, second_opt): (i32, i32, Option<i32>),
            // secfrac: Option<NonEmptyDigitsString>,
            // tz: As2TimeOffset,
            F: Fn(
                &str,
                NaiveDate,
                (u32, u32, Option<u32>),
                Option<NonEmptyDigitsString>,
                &As2TimeOffset,
            ),
        {
            // Check for each:
            //  * timezone: positive, negative, Z, `-00:00`.
            //  * omit_second: true, false
            //  * omit_secfrac: true, false
            let timezones = &[
                (
                    "+09:10",
                    As2TimeOffset::KnownLocal(
                        As2TimeNumOffset::new_positive(9, 10).expect("Should never fail"),
                    ),
                ),
                (
                    "-18:45",
                    As2TimeOffset::KnownLocal(
                        As2TimeNumOffset::new_negative(18, 45).expect("Should never fail"),
                    ),
                ),
                ("-00:00", As2TimeOffset::UnknownLocal),
                (
                    "+00:00",
                    As2TimeOffset::KnownLocal(
                        As2TimeNumOffset::new_negative(0, 0).expect("Should never fail"),
                    ),
                ),
                ("Z", As2TimeOffset::Z),
            ];
            let seconds = &[(":40", Some(40)), (":01", Some(1)), ("", None)];
            let secfracs = &["0", "00001", "1230000", ""];

            for (tz_str, tz) in timezones {
                for (second_str, second) in seconds {
                    for &secfrac_str in secfracs {
                        let secfrac = if secfrac_str.is_empty() {
                            None
                        } else {
                            Some(NonEmptyDigitsString::new(secfrac_str).expect("Should never fail"))
                        };
                        let secfrac_str = secfrac
                            .as_ref()
                            .map(|s| format!(".{}", s))
                            .unwrap_or_else(String::new);

                        const YEAR: i32 = 1999;
                        const MONTH: u32 = 12;
                        const DAY: u32 = 31;
                        const HOUR: u32 = 23;
                        const MINUTE: u32 = 59;
                        let datetime_str = format!(
                            "{:02}-{:02}-{:02}T{:02}:{:02}{}{}{}",
                            YEAR, MONTH, DAY, HOUR, MINUTE, second_str, secfrac_str, tz_str
                        );
                        eprintln!("datetime_str = {}", datetime_str);
                        let naive_date = NaiveDate::from_ymd(YEAR, MONTH, DAY);

                        for_case(
                            &datetime_str,
                            naive_date,
                            (HOUR, MINUTE, *second),
                            secfrac,
                            tz,
                        );
                    }
                }
            }
        }

        #[test]
        fn from_str_display() {
            test_for_cases(
                |datetime_str, naive_date, (hour, minute, second_opt), secfrac, tz| {
                    use chrono::TimeZone;

                    let datetime_parsed: As2DateTime =
                        datetime_str.parse().expect("Should never fail");
                    assert_eq!(datetime_parsed.to_string(), datetime_str);

                    let naive_local =
                        naive_date.and_hms_nano(hour, minute, second_opt.unwrap_or(0), 0);
                    let datetime_direct = As2DateTime::new(
                        tz.from_local_datetime(&naive_local)
                            .single()
                            .expect("Should never fail"),
                        second_opt.is_none(),
                        secfrac,
                    );
                    assert_eq!(datetime_parsed, datetime_direct);
                },
            );
        }
    }
}
