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

//! pgnumeric benchmark

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pgnumeric::{NumericBuf, NumericTryFromError};
use std::convert::{TryFrom, TryInto};

fn parse(s: &str) -> NumericBuf {
    s.parse().unwrap()
}

fn parse_benchmark(c: &mut Criterion) {
    c.bench_function("parse_nan", |b| {
        b.iter(|| {
            let _n = parse(black_box("NaN"));
        })
    });
    c.bench_function("parse_u8", |b| {
        b.iter(|| {
            let _n = parse(black_box("255"));
        })
    });
    c.bench_function("parse_u16", |b| {
        b.iter(|| {
            let _n = parse(black_box("65535"));
        })
    });
    c.bench_function("parse_u32", |b| {
        b.iter(|| {
            let _n = parse(black_box("4294967295"));
        })
    });
    c.bench_function("parse_u64", |b| {
        b.iter(|| {
            let _n = parse(black_box("18446744073709551615"));
        })
    });
    c.bench_function("parse_u128", |b| {
        b.iter(|| {
            let _n = parse(black_box("340282366920938463463374607431768211455"));
        })
    });
    c.bench_function("parse_f32", |b| {
        b.iter(|| {
            let _n = parse(black_box("1.23456789e10"));
        })
    });
    c.bench_function("parse_f64", |b| {
        b.iter(|| {
            let _n = parse(black_box("1.234567890123456789e10"));
        })
    });
}

fn into<'a, T: TryFrom<&'a NumericBuf, Error = NumericTryFromError>>(val: &'a NumericBuf) -> T {
    TryFrom::try_from(val).unwrap()
}

fn into_benchmark(c: &mut Criterion) {
    c.bench_function("to_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n: u8 = into(black_box(&val));
        })
    });
    c.bench_function("to_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n: u16 = into(black_box(&val));
        })
    });
    c.bench_function("to_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n: u32 = into(black_box(&val));
        })
    });
    c.bench_function("to_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n: u64 = into(black_box(&val));
        })
    });
    c.bench_function("to_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n: u128 = into(black_box(&val));
        })
    });
    c.bench_function("to_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n: f32 = into(black_box(&val));
        })
    });
    c.bench_function("to_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n: f64 = into(black_box(&val));
        })
    });
}

fn from<T: Into<NumericBuf>>(val: T) -> NumericBuf {
    val.into()
}

fn try_from<T: TryInto<NumericBuf, Error = NumericTryFromError>>(val: T) -> NumericBuf {
    val.try_into().unwrap()
}

fn from_benchmark(c: &mut Criterion) {
    c.bench_function("from_u8", |b| {
        b.iter(|| {
            let _n = from(black_box(255_u8));
        })
    });
    c.bench_function("from_u16", |b| {
        b.iter(|| {
            let _n = from(black_box(65535_u16));
        })
    });
    c.bench_function("from_u32", |b| {
        b.iter(|| {
            let _n = from(black_box(4294967295_u32));
        })
    });
    c.bench_function("from_u64", |b| {
        b.iter(|| {
            let _n = from(black_box(18446744073709551615_u64));
        })
    });
    c.bench_function("from_u128", |b| {
        b.iter(|| {
            let _n = from(black_box(340282366920938463463374607431768211455_u128));
        })
    });
    c.bench_function("from_f32", |b| {
        b.iter(|| {
            let _n = try_from(black_box(1.23456789e10_f32));
        })
    });
    c.bench_function("from_f64", |b| {
        b.iter(|| {
            let _n = try_from(black_box(1.234567890123456789e10_f64));
        })
    });
}

fn fmt(val: &NumericBuf) -> String {
    format!("{}", val)
}

fn fmt_benchmark(c: &mut Criterion) {
    c.bench_function("fmt_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
    c.bench_function("fmt_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = fmt(black_box(&val));
        })
    });
}

fn fmt_sci(val: &NumericBuf) -> String {
    format!("{:e}", val)
}

fn fmt_sci_benchmark(c: &mut Criterion) {
    c.bench_function("fmt_sci_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
    c.bench_function("fmt_sci_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = fmt_sci(black_box(&val));
        })
    });
}

fn add(x: &NumericBuf, y: &NumericBuf) -> NumericBuf {
    x + y
}

fn add_benchmark(c: &mut Criterion) {
    c.bench_function("add_u8", |b| {
        let x = parse("127");
        let y = parse("12");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_u16", |b| {
        let x = parse("32767");
        let y = parse("3276");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_u32", |b| {
        let x = parse("2147483647");
        let y = parse("214748364");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_u64", |b| {
        let x = parse("9223372036854775807");
        let y = parse("922337203685477580");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_u128", |b| {
        let x = parse("170141183460469231731687303715884105727");
        let y = parse("17014118346046923173168730371588410572");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_f32", |b| {
        let x = parse("1.23456789e10");
        let y = parse("1.23456789e9");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("add_f64", |b| {
        let x = parse("1.234567890123456789e10");
        let y = parse("1.234567890123456789e9");
        b.iter(|| {
            let _n = add(black_box(&x), black_box(&y));
        })
    });
}

fn sub(x: &NumericBuf, y: &NumericBuf) -> NumericBuf {
    x - y
}

fn sub_benchmark(c: &mut Criterion) {
    c.bench_function("sub_u8", |b| {
        let x = parse("127");
        let y = parse("12");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_u16", |b| {
        let x = parse("32767");
        let y = parse("3276");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_u32", |b| {
        let x = parse("2147483647");
        let y = parse("214748364");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_u64", |b| {
        let x = parse("9223372036854775807");
        let y = parse("922337203685477580");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_u128", |b| {
        let x = parse("170141183460469231731687303715884105727");
        let y = parse("17014118346046923173168730371588410572");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_f32", |b| {
        let x = parse("1.23456789e10");
        let y = parse("1.23456789e9");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("sub_f64", |b| {
        let x = parse("1.234567890123456789e10");
        let y = parse("1.234567890123456789e9");
        b.iter(|| {
            let _n = sub(black_box(&x), black_box(&y));
        })
    });
}

fn mul(x: &NumericBuf, y: &NumericBuf) -> NumericBuf {
    x * y
}

fn mul_benchmark(c: &mut Criterion) {
    c.bench_function("mul_u8", |b| {
        let x = parse("127");
        let y = parse("12");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_u16", |b| {
        let x = parse("32767");
        let y = parse("3276");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_u32", |b| {
        let x = parse("2147483647");
        let y = parse("214748364");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_u64", |b| {
        let x = parse("9223372036854775807");
        let y = parse("922337203685477580");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_u128", |b| {
        let x = parse("170141183460469231731687303715884105727");
        let y = parse("17014118346046923173168730371588410572");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_f32", |b| {
        let x = parse("1.23456789e10");
        let y = parse("1.23456789e9");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("mul_f64", |b| {
        let x = parse("1.234567890123456789e10");
        let y = parse("1.234567890123456789e9");
        b.iter(|| {
            let _n = mul(black_box(&x), black_box(&y));
        })
    });
}

fn div(x: &NumericBuf, y: &NumericBuf) -> NumericBuf {
    x / y
}

fn div_benchmark(c: &mut Criterion) {
    c.bench_function("div_u8", |b| {
        let x = parse("127");
        let y = parse("12");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_u16", |b| {
        let x = parse("32767");
        let y = parse("3276");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_u32", |b| {
        let x = parse("2147483647");
        let y = parse("214748364");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_u64", |b| {
        let x = parse("9223372036854775807");
        let y = parse("922337203685477580");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_u128", |b| {
        let x = parse("170141183460469231731687303715884105727");
        let y = parse("17014118346046923173168730371588410572");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_f32", |b| {
        let x = parse("1.23456789e10");
        let y = parse("1.23456789e9");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("div_f64", |b| {
        let x = parse("1.234567890123456789e10");
        let y = parse("1.234567890123456789e9");
        b.iter(|| {
            let _n = div(black_box(&x), black_box(&y));
        })
    });
}

fn rem(x: &NumericBuf, y: &NumericBuf) -> NumericBuf {
    x / y
}

fn rem_benchmark(c: &mut Criterion) {
    c.bench_function("rem_u8", |b| {
        let x = parse("127");
        let y = parse("12");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_u16", |b| {
        let x = parse("32767");
        let y = parse("3276");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_u32", |b| {
        let x = parse("2147483647");
        let y = parse("214748364");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_u64", |b| {
        let x = parse("9223372036854775807");
        let y = parse("922337203685477580");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_u128", |b| {
        let x = parse("170141183460469231731687303715884105727");
        let y = parse("17014118346046923173168730371588410572");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_f32", |b| {
        let x = parse("1.23456789e10");
        let y = parse("1.23456789e9");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
    c.bench_function("rem_f64", |b| {
        let x = parse("1.234567890123456789e10");
        let y = parse("1.234567890123456789e9");
        b.iter(|| {
            let _n = rem(black_box(&x), black_box(&y));
        })
    });
}

fn neg_benchmark(c: &mut Criterion) {
    c.bench_function("neg_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
    c.bench_function("neg_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = -black_box(&val);
        })
    });
}

fn neg_mut_benchmark(c: &mut Criterion) {
    c.bench_function("neg_mut_u8", |b| {
        let mut val = parse("255");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_u16", |b| {
        let mut val = parse("65535");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_u32", |b| {
        let mut val = parse("4294967295");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_u64", |b| {
        let mut val = parse("18446744073709551615");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_u128", |b| {
        let mut val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_f32", |b| {
        let mut val = parse("1.23456789e10");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
    c.bench_function("neg_mut_f64", |b| {
        let mut val = parse("1.234567890123456789e10");
        b.iter(|| {
            black_box(&mut val).negate_mut();
        })
    });
}

fn abs_benchmark(c: &mut Criterion) {
    c.bench_function("abs_nan", |b| {
        let mut val = parse("NaN");
        b.iter(|| {
            black_box(&mut val).abs();
        })
    });
    c.bench_function("abs_pos", |b| {
        let mut val = parse("4294967295");
        b.iter(|| {
            black_box(&mut val).abs();
        })
    });
    c.bench_function("abs_neg", |b| {
        let mut val = parse("-4294967295");
        b.iter(|| {
            black_box(&mut val).abs();
        })
    });
}

fn sqrt_benchmark(c: &mut Criterion) {
    c.bench_function("sqrt_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
    c.bench_function("sqrt_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = black_box(&val).sqrt();
        })
    });
}

fn ln_benchmark(c: &mut Criterion) {
    c.bench_function("ln_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
    c.bench_function("ln_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = black_box(&val).ln();
        })
    });
}

fn log2_benchmark(c: &mut Criterion) {
    c.bench_function("log2_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
    c.bench_function("log2_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = black_box(&val).log2();
        })
    });
}

fn log10_benchmark(c: &mut Criterion) {
    c.bench_function("log10_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
    c.bench_function("log10_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            let _n = black_box(&val).log10();
        })
    });
}

fn exp_benchmark(c: &mut Criterion) {
    c.bench_function("exp_1", |b| {
        let val = parse("1");
        b.iter(|| {
            let _n = black_box(&val).exp();
        })
    });
    c.bench_function("exp_10", |b| {
        let val = parse("10");
        b.iter(|| {
            let _n = black_box(&val).exp();
        })
    });
    c.bench_function("exp_100", |b| {
        let val = parse("100");
        b.iter(|| {
            let _n = black_box(&val).exp();
        })
    });
    c.bench_function("exp_1000", |b| {
        let val = parse("1000");
        b.iter(|| {
            let _n = black_box(&val).exp();
        })
    });
    c.bench_function("exp_2000", |b| {
        let val = parse("2000");
        b.iter(|| {
            let _n = black_box(&val).exp();
        })
    });
}

fn pow_benchmark(c: &mut Criterion) {
    c.bench_function("pow_10_1", |b| {
        let val = parse("10");
        let exp = parse("1");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
    c.bench_function("pow_10_10", |b| {
        let val = parse("10");
        let exp = parse("10");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
    c.bench_function("pow_10_100", |b| {
        let val = parse("10");
        let exp = parse("100");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
    c.bench_function("pow_10_1000", |b| {
        let val = parse("10");
        let exp = parse("1000");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
    c.bench_function("pow_10_5000", |b| {
        let val = parse("10");
        let exp = parse("5000");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
    c.bench_function("pow_5000_10", |b| {
        let val = parse("5000");
        let exp = parse("10");
        b.iter(|| {
            let _n = black_box(&val).pow(&exp);
        })
    });
}

fn fac_benchmark(c: &mut Criterion) {
    c.bench_function("fac_1", |b| {
        b.iter(|| {
            let _n = NumericBuf::factorial(black_box(1));
        })
    });
    c.bench_function("fac_2", |b| {
        b.iter(|| {
            let _n = NumericBuf::factorial(black_box(2));
        })
    });
    c.bench_function("fac_10", |b| {
        b.iter(|| {
            let _n = NumericBuf::factorial(black_box(10));
        })
    });
    c.bench_function("fac_100", |b| {
        b.iter(|| {
            let _n = NumericBuf::factorial(black_box(100));
        })
    });
    c.bench_function("fac_1000", |b| {
        b.iter(|| {
            let _n = NumericBuf::factorial(black_box(1000));
        })
    });
}

fn round_benchmark(c: &mut Criterion) {
    c.bench_function("round_u8", |b| {
        let mut val = parse("255");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_u16", |b| {
        let mut val = parse("65535");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_u32", |b| {
        let mut val = parse("4294967295");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_u64", |b| {
        let mut val = parse("18446744073709551615");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_u128", |b| {
        let mut val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_f32", |b| {
        let mut val = parse("1.23456789e10");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
    c.bench_function("round_f64", |b| {
        let mut val = parse("1.234567890123456789e10");
        b.iter(|| {
            black_box(&mut val).round_mut(0);
        })
    });
}

fn trunc_benchmark(c: &mut Criterion) {
    c.bench_function("trunc_u8", |b| {
        let mut val = parse("255");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_u16", |b| {
        let mut val = parse("65535");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_u32", |b| {
        let mut val = parse("4294967295");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_u64", |b| {
        let mut val = parse("18446744073709551615");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_u128", |b| {
        let mut val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_f32", |b| {
        let mut val = parse("1.23456789e10");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
    c.bench_function("trunc_f64", |b| {
        let mut val = parse("1.234567890123456789e10");
        b.iter(|| {
            black_box(&mut val).trunc_mut(0);
        })
    });
}

fn ceil_benchmark(c: &mut Criterion) {
    c.bench_function("ceil_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
    c.bench_function("ceil_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            black_box(&val).ceil();
        })
    });
}

fn floor_benchmark(c: &mut Criterion) {
    c.bench_function("floor_u8", |b| {
        let val = parse("255");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_u16", |b| {
        let val = parse("65535");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_u32", |b| {
        let val = parse("4294967295");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_u64", |b| {
        let val = parse("18446744073709551615");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_u128", |b| {
        let val = parse("340282366920938463463374607431768211455");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_f32", |b| {
        let val = parse("1.23456789e10");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
    c.bench_function("floor_f64", |b| {
        let val = parse("1.234567890123456789e10");
        b.iter(|| {
            black_box(&val).floor();
        })
    });
}

criterion_group!(
    benches,
    parse_benchmark,
    into_benchmark,
    from_benchmark,
    fmt_benchmark,
    fmt_sci_benchmark,
    add_benchmark,
    sub_benchmark,
    mul_benchmark,
    div_benchmark,
    rem_benchmark,
    neg_benchmark,
    neg_mut_benchmark,
    abs_benchmark,
    sqrt_benchmark,
    ln_benchmark,
    log2_benchmark,
    log10_benchmark,
    exp_benchmark,
    pow_benchmark,
    fac_benchmark,
    round_benchmark,
    trunc_benchmark,
    ceil_benchmark,
    floor_benchmark,
);
criterion_main!(benches);
