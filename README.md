# pgnumeric

[![Apache-2.0 licensed](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.43+-lightgray.svg)](README.md#rust-version-requirements)
[![Crate](https://img.shields.io/crates/v/pgnumeric.svg)](https://crates.io/crates/pgnumeric)
[![API](https://docs.rs/pgnumeric/badge.svg)](https://docs.rs/pgnumeric)

Arbitrary precision numeric implementation written in Rust, compatible with PostgreSQL's numeric.

See also: [PostgreSQL Arbitrary Precision Numbers](https://www.postgresql.org/docs/current/datatype-numeric.html#DATATYPE-NUMERIC-DECIMAL)

This crate provides two types, [`NumericBuf`] and [`Numeric`].

## Usage

To build a numeric, use `NumericBuf`:

```Rust
use pgnumeric::NumericBuf;

let n1: NumericBuf = "123".parse().unwrap();
let n2: NumericBuf = "456".parse().unwrap();
let result = n1 + n2;
assert_eq!(result.to_string(), "579");
```

To build a numeric from Rust primitive types:

```Rust
use pgnumeric::NumericBuf;

let n1: NumericBuf = From::from(123_i32);
let n2: NumericBuf = From::from(456_i32);
let result = n1 + n2;
assert_eq!(result, Into::<NumericBuf>::into(579_i32));
```

Numeric supports high precision arithmetic operations.

```Rust
use pgnumeric::NumericBuf;

let n1: NumericBuf = "123456789.987654321".parse().unwrap();
let n2: NumericBuf = "987654321.123456789".parse().unwrap();
let result = n1 * n2;
assert_eq!(result.to_string(), "121932632103337905.662094193112635269");

let n3 = "170141183460469231731687303715884105727".parse::<NumericBuf>().unwrap();
assert_eq!(n3.sqrt().to_string(), "13043817825332782212")
```

Numeric can be serialized to bytes slice and deserialized from bytes slice.

```Rust
use pgnumeric::{NumericBuf, Numeric};

let n1 = "123456789.987654321".parse::<NumericBuf>().unwrap();
let bytes = n1.as_bytes();
let n2 = unsafe { Numeric::from_bytes_unchecked(bytes) };
assert_eq!(n1, n2);
```

## Rust version requirements

`pgnumeric` works on rust `1.43`.

## License

This project is licensed under the Apache-2.0 license ([LICENSE](LICENSE) or http://www.apache.org/licenses/LICENSE-2.0).

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `pgnumeric` by you, shall be licensed as Apache-2.0, without any additional
terms or conditions.
