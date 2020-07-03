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

//! Arbitrary precision numeric, compatible with PostgreSQL's numeric.
//!
//! This crate provides two types, `NumericBuf` and `Numeric`.
//!
//! ## Optional features
//!
//! ### `serde`
//!
//! When this optional dependency is enabled, `NumericBuf` and `Numeric` implement the `serde::Serialize` and
//! `serde::Deserialize` traits.
//!
//! ## Usage
//!
//! To build a numeric, use [`NumericBuf`]:
//!
//! ```
//! use pgnumeric::NumericBuf;
//!
//! let n1: NumericBuf = "123".parse().unwrap();
//! let n2: NumericBuf = "456".parse().unwrap();
//! let result = n1 + n2;
//! assert_eq!(result.to_string(), "579");
//! ```
//!
//! To build a numeric from Rust primitive types:
//!
//! ```
//! use pgnumeric::NumericBuf;
//!
//! let n1: NumericBuf = From::from(123_i32);
//! let n2: NumericBuf = From::from(456_i32);
//! let result = n1 + n2;
//! assert_eq!(result, Into::<NumericBuf>::into(579_i32));
//! ```
//!
//! Numeric supports high precision arithmetic operations.
//!
//! ```
//! use pgnumeric::NumericBuf;
//!
//! let n1: NumericBuf = "123456789.987654321".parse().unwrap();
//! let n2: NumericBuf = "987654321.123456789".parse().unwrap();
//! let result = n1 * n2;
//! assert_eq!(result.to_string(), "121932632103337905.662094193112635269");
//!
//! let n3 = "170141183460469231731687303715884105727".parse::<NumericBuf>().unwrap();
//! assert_eq!(n3.sqrt().to_string(), "13043817825332782212")
//! ```
//!
//! Numeric can be serialized to bytes slice and deserialized from bytes slice.
//!
//! ```
//! use pgnumeric::{NumericBuf, Numeric};
//!
//! let n1 = "123456789.987654321".parse::<NumericBuf>().unwrap();
//! let bytes = n1.as_bytes();
//! let n2 = unsafe { Numeric::from_bytes_unchecked(bytes) };
//! assert_eq!(n1, n2);
//! ```

mod binary;
mod convert;
mod data;
mod error;
mod num;
mod ops;
mod parse;
mod typmod;
mod var;

pub use crate::error::{NumericParseError, NumericTryFromError};
pub use crate::num::{Numeric, NumericBuf};
pub use crate::typmod::Typmod;
