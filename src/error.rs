// Copyright 2020 CoD Technologies Corp.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Numeric error handling.

use std::error::Error;
use std::fmt;
use std::num::ParseFloatError;

/// An error which can be returned when parsing a numeric.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumericParseError {
    kind: ParseErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ParseErrorKind {
    Empty,
    Invalid,
    Overflow,
}

impl fmt::Display for NumericParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.kind {
            ParseErrorKind::Empty => write!(f, "cannot parse numeric from empty string"),
            ParseErrorKind::Invalid => write!(f, "invalid numeric literal"),
            ParseErrorKind::Overflow => write!(f, "value overflows numeric format"),
        }
    }
}

impl Error for NumericParseError {}

impl NumericParseError {
    #[inline]
    pub(crate) const fn new(kind: ParseErrorKind) -> Self {
        NumericParseError { kind }
    }

    #[inline]
    pub(crate) const fn empty() -> Self {
        Self::new(ParseErrorKind::Empty)
    }

    #[inline]
    pub(crate) const fn invalid() -> Self {
        Self::new(ParseErrorKind::Invalid)
    }

    #[inline]
    pub(crate) const fn overflow() -> Self {
        Self::new(ParseErrorKind::Overflow)
    }
}

/// An error which can be returned when a conversion from other type to numeric fails.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumericTryFromError {
    kind: TryFromErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TryFromErrorKind {
    Invalid,
    Overflow,
}

impl fmt::Display for NumericTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.kind {
            TryFromErrorKind::Invalid => write!(f, "cannot convert to numeric"),
            TryFromErrorKind::Overflow => write!(f, "value is out of range"),
        }
    }
}

impl Error for NumericTryFromError {}

impl NumericTryFromError {
    #[inline]
    const fn new(kind: TryFromErrorKind) -> Self {
        NumericTryFromError { kind }
    }

    #[inline]
    pub(crate) const fn invalid() -> Self {
        Self::new(TryFromErrorKind::Invalid)
    }

    #[inline]
    pub(crate) const fn overflow() -> Self {
        Self::new(TryFromErrorKind::Overflow)
    }
}

impl From<NumericParseError> for NumericTryFromError {
    fn from(e: NumericParseError) -> Self {
        match e.kind {
            ParseErrorKind::Empty | ParseErrorKind::Invalid => NumericTryFromError::invalid(),
            ParseErrorKind::Overflow => NumericTryFromError::overflow(),
        }
    }
}

impl From<ParseFloatError> for NumericTryFromError {
    fn from(_: ParseFloatError) -> Self {
        NumericTryFromError::invalid()
    }
}
