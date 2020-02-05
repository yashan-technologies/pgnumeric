// Copyright 2020 CoD Team

use std::error::Error;
use std::fmt;

/// An error which can be returned when parsing a numeric.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseNumericError {
    kind: NumericErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NumericErrorKind {
    Empty,
    Invalid,
    Overflow,
}

impl fmt::Display for ParseNumericError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.kind {
            NumericErrorKind::Empty => write!(f, "cannot parse numeric from empty string"),
            NumericErrorKind::Invalid => write!(f, "invalid numeric literal"),
            NumericErrorKind::Overflow => write!(f, "value overflows numeric format"),
        }
    }
}

impl Error for ParseNumericError {}

impl ParseNumericError {
    #[inline]
    pub(crate) const fn new(kind: NumericErrorKind) -> Self {
        ParseNumericError { kind }
    }

    #[inline]
    pub(crate) const fn empty() -> Self {
        Self::new(NumericErrorKind::Empty)
    }

    #[inline]
    pub(crate) const fn invalid() -> Self {
        Self::new(NumericErrorKind::Invalid)
    }

    #[inline]
    pub(crate) const fn overflow() -> Self {
        Self::new(NumericErrorKind::Overflow)
    }
}
