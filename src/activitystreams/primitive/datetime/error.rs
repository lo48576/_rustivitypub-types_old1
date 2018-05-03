//! Error types for datetime module.

use std::error;
use std::fmt;


/// A type for errors on datetime creation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DateTimeCreationError {
    /// Invalid format.
    InvalidFormat,
    /// Timezone is not specified.
    NoTimeZone,
    /// Offset creation or conversion error.
    Offset(TimeOffsetError),
}

impl fmt::Display for DateTimeCreationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::error::Error;

        match *self {
            DateTimeCreationError::InvalidFormat | DateTimeCreationError::NoTimeZone => {
                f.write_str(self.description())
            },
            DateTimeCreationError::Offset(ref e) => write!(f, "{}: {}", self.description(), e),
        }
    }
}

impl error::Error for DateTimeCreationError {
    fn description(&self) -> &str {
        match *self {
            DateTimeCreationError::InvalidFormat => "Invalid format",
            DateTimeCreationError::NoTimeZone => "Timezone is not specified",
            DateTimeCreationError::Offset(_) => "Failed to create or convert time offset",
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            DateTimeCreationError::Offset(ref e) => Some(e),
            _ => None,
        }
    }
}

impl From<TimeOffsetError> for DateTimeCreationError {
    fn from(e: TimeOffsetError) -> Self {
        DateTimeCreationError::Offset(e)
    }
}


/// A type for `As2TimeNumOffset` and `As2TimeOffset` creation error.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TimeOffsetError {
    /// Format error.
    InvalidFormat,
    /// The given hour part value was invalid.
    // Use `i16` to represent `i8` value and `u8` value without overflow.
    InvalidHourPart(i16),
    /// The given minute part value was invalid.
    InvalidMinutePart(u8),
    /// The given minutes offset was invalid.
    MinutesOutOfRange(i16),
    /// Second part specified.
    NonZeroSecond,
    /// Failed to get offset from timezone.
    TimezoneConversionFailure,
}

impl error::Error for TimeOffsetError {
    fn description(&self) -> &str {
        match *self {
            TimeOffsetError::InvalidFormat => "Parse error due to invalid format",
            TimeOffsetError::InvalidHourPart(_) => "Invalid hour part value",
            TimeOffsetError::InvalidMinutePart(_) => "Invalid minute part value",
            TimeOffsetError::MinutesOutOfRange(_) => "Minutes offset out of range",
            TimeOffsetError::NonZeroSecond => "Second part should be 0 but was not",
            TimeOffsetError::TimezoneConversionFailure => "Failed to get offset from timezone",
        }
    }
}

impl fmt::Display for TimeOffsetError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TimeOffsetError::InvalidFormat => f.write_str("Parse error due to invalid format"),
            TimeOffsetError::InvalidHourPart(hour) => {
                write!(f, "Invalid hour part value `{}`", hour)
            },
            TimeOffsetError::InvalidMinutePart(minute) => {
                write!(f, "Invalid minute part value `{}`", minute)
            },
            TimeOffsetError::MinutesOutOfRange(minutes) => {
                write!(f, "Minutes offset `{}` out of range", minutes)
            },
            TimeOffsetError::NonZeroSecond => f.write_str("Second part should be 0 but was not"),
            TimeOffsetError::TimezoneConversionFailure => {
                f.write_str("Failed to get offset from timezone")
            },
        }
    }
}
