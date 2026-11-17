#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] f64_to_bits verus_code! {
        use vstd::prelude::*;
        use vstd::float::FloatBitsProperties;

        fn test_values() {
            let a = 1.0f64.to_bits();
            assert(a == 0x3ff0_0000_0000_0000u64);
            let b = (-0.0f64).to_bits();
            assert(b == 0x8000_0000_0000_0000u64);
            let c = 0.0f64.to_bits();
            assert(c == 0);
            let d = 1.0f32.to_bits();
            assert(d == 0x3f80_0000u32);
        }

        fn test_classes() {
            assert(1.0f64.is_finite());
            let a = 1.0f64.is_finite();
            assert(a);
            let b = 1.0f64.is_nan();
            assert(!b);
            let c = (-0.0f64).is_sign_negative();
            assert(c);
            let d = 0.0f64.is_sign_positive();
            assert(d);
            let e = (-2.5f32).is_sign_positive();
            assert(!e);
            let f = 2.5f32.is_infinite();
            assert(!f);
        }

        // A sort key in the style of SQLite's: the sign bit decides how the rest of
        // the bits are ordered.
        fn sort_key(x: f64) -> (k: u64)
            ensures
                x.is_sign_negative() ==> k == !x.to_bits(),
                !x.is_sign_negative() ==> k == x.to_bits() | 0x8000_0000_0000_0000u64,
        {
            let b = x.to_bits();
            if x.is_sign_negative() {
                !b
            } else {
                b | 0x8000_0000_0000_0000u64
            }
        }

        fn test_sign_bit(x: f64) {
            let b = x.to_bits();
            let neg = x.is_sign_negative();
            assert(neg <==> b >= 0x8000_0000_0000_0000u64);
            assert(neg <==> (b >> 63u64) == 1u64) by (bit_vector)
                requires neg <==> b >= 0x8000_0000_0000_0000u64;
        }

        fn test_exclusive(x: f32) {
            let n = x.is_nan();
            let i = x.is_infinite();
            let f = x.is_finite();
            assert(n ==> !i && !f);
            assert(i ==> !f);
            assert(n || i || f);
            let p = x.is_sign_positive();
            let m = x.is_sign_negative();
            assert(p != m);
        }

        spec fn spec_bits(x: f64) -> u64 {
            x.to_bits()
        }

        proof fn test_spec(x: f64) {
            assert(spec_bits(x) == f64_to_bits(x));
            assert(x.is_nan() == x.is_nan_spec());
        }

        fn test_no_unwind(x: f64, y: f32)
            no_unwind
        {
            let _ = x.to_bits();
            let _ = x.is_nan();
            let _ = x.is_infinite();
            let _ = x.is_finite();
            let _ = y.is_sign_negative();
            let _ = y.is_sign_positive();
        }

        fn test_wrong(x: f64) {
            let b = x.to_bits();
            assert(b < 0x8000_0000_0000_0000u64); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
