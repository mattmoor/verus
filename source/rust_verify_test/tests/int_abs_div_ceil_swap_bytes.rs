#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] signed_abs verus_code! {
        use vstd::prelude::*;

        fn test_values() {
            let a = (-5i8).abs();
            assert(a == 5);
            let b = 7i32.abs();
            assert(b == 7);
            let c = i8::MIN.unsigned_abs();
            assert(c == 128u8);
            let d = (-100i8).abs_diff(100);
            assert(d == 200u8);
            let e = i64::MIN.abs_diff(i64::MAX);
            assert(e == u64::MAX);
            let f = (-3i16).unsigned_abs();
            assert(f == 3u16);
        }

        fn test_generic(x: i32, y: isize, z: i128)
            requires
                x != i32::MIN,
                y > isize::MIN,
        {
            let a = x.abs();
            assert(a >= 0 && (a == x || a == -x));
            let b = y.abs();
            assert(b as int == if y < 0 { -y } else { y as int });
            let c = z.unsigned_abs();
            assert(c as int == if z < 0 { -z } else { z as int });
            let d = z.abs_diff(z);
            assert(d == 0);
        }

        spec fn spec_abs(x: i16) -> i16 {
            x.abs()
        }

        proof fn test_spec() {
            assert(spec_abs(-4i16) == 4i16);
            assert((-9i64).unsigned_abs() == 9u64);
            assert(2i8.abs_diff(-2i8) == 4u8);
        }

        fn test_no_unwind(a: i8, b: i64)
            requires a != i8::MIN,
            no_unwind
        {
            let _ = a.abs();
            let _ = b.unsigned_abs();
            let _ = b.abs_diff(b);
        }

        fn test_min_fails() {
            let a = i8::MIN.abs(); // FAILS
        }

        fn test_wrong(x: i8) {
            let a = x.unsigned_abs();
            assert(a as int == x); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] unsigned_div_ceil_abs_diff verus_code! {
        use vstd::prelude::*;

        fn test_values() {
            let a = 7u32.div_ceil(2);
            assert(a == 4);
            let b = 8u32.div_ceil(2);
            assert(b == 4);
            let c = 0u8.div_ceil(3);
            assert(c == 0);
            let d = u64::MAX.div_ceil(1);
            assert(d == u64::MAX);
            let e = u64::MAX.div_ceil(2);
            assert(e == 0x8000_0000_0000_0000u64);
            let f = 3u16.abs_diff(10);
            assert(f == 7);
            let g = 10u16.abs_diff(3);
            assert(g == 7);
        }

        fn test_generic(n: usize, k: u128)
            requires k > 0,
        {
            // Number of 8-byte words needed to hold n bytes.
            let w = n.div_ceil(8);
            assert(w * 8 >= n);
            assert(w * 8 < n + 8);
            let q = k.div_ceil(k);
            assert(q == 1);
        }

        spec fn spec_div_ceil(x: u32, y: u32) -> u32
            recommends y != 0,
        {
            x.div_ceil(y)
        }

        proof fn test_spec() {
            assert(spec_div_ceil(10, 3) == 4);
            assert(5u8.abs_diff(9) == 4u8);
        }

        fn test_no_unwind(a: u8, b: u64)
            requires b != 0,
            no_unwind
        {
            let _ = a.abs_diff(a);
            let _ = a.div_ceil(1);
            let _ = b.div_ceil(b);
        }

        fn test_zero_fails(x: u32) {
            let a = x.div_ceil(0); // FAILS
        }

        fn test_wrong(x: u32) {
            let a = x.div_ceil(4);
            assert(a == x / 4); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

test_verify_one_file! {
    #[test] swap_bytes verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::num::*;

        fn test_values() {
            let a = 0x1234u16.swap_bytes();
            assert(0x1234u16.swap_bytes() == 0x3412u16) by (compute);
            assert(a == 0x3412u16);
            let b = 0x1234_5678u32.swap_bytes();
            assert(0x1234_5678u32.swap_bytes() == 0x7856_3412u32) by (compute);
            assert(b == 0x7856_3412u32);
            assert(0x0102_0304_0506_0708u64.swap_bytes() == 0x0807_0605_0403_0201u64)
                by (compute);
            assert(0x0102_0304_0506_0708_090a_0b0c_0d0e_0f10u128.swap_bytes()
                == 0x100f_0e0d_0c0b_0a09_0807_0605_0403_0201u128) by (compute);
            let e = 0xabu8.swap_bytes();
            assert(e == 0xab);
        }

        fn test_signed() {
            // The signed spec casts through the unsigned one, and only bit_vector
            // evaluates a cast of an out-of-range value.
            let a = 0x0102i16.swap_bytes();
            assert(a == u16_swap_bytes(0x0102u16) as i16);
            assert(0x0102u16.swap_bytes() == 0x0201u16) by (compute);
            assert(a == 0x0201i16);
            let b = 0x0000_0080i32.swap_bytes();
            assert(0x0000_0080u32.swap_bytes() == 0x8000_0000u32) by (compute);
            assert(b == 0x8000_0000u32 as i32);
            assert(0x8000_0000u32 as i32 == i32::MIN) by (bit_vector);
            assert(b == i32::MIN);
        }

        proof fn lemma_u16_swap_twice(x: u16)
            ensures
                u16_swap_bytes(u16_swap_bytes(x)) == x,
        {
            assert(((((x & 0xff) << 8u32) | ((x >> 8u32) & 0xff)) & 0xff) << 8u32
                | ((((x & 0xff) << 8u32) | ((x >> 8u32) & 0xff)) >> 8u32) & 0xff == x)
                by (bit_vector);
        }

        fn test_u16_round_trip(x: u16) {
            let a = x.swap_bytes();
            let b = a.swap_bytes();
            proof {
                lemma_u16_swap_twice(x);
            }
            assert(b == x);
        }

        fn test_u32_low_byte(x: u32) {
            // The low byte of the result is the high byte of x.
            let s = x.swap_bytes();
            assert(s & 0xff == x >> 24u32) by (bit_vector)
                requires
                    s == ((x & 0xff) << 24u32) | (((x >> 8u32) & 0xff) << 16u32) | (((x >> 16u32)
                        & 0xff) << 8u32) | ((x >> 24u32) & 0xff),
            ;
        }

        spec fn spec_swap(x: u32) -> u32 {
            x.swap_bytes()
        }

        proof fn test_spec() {
            assert(spec_swap(0xaabb_ccddu32) == 0xddcc_bbaau32) by (compute);
        }

        fn test_no_unwind(a: u8, b: u64, c: usize, d: i128)
            no_unwind
        {
            let _ = a.swap_bytes();
            let _ = b.swap_bytes();
            let _ = c.swap_bytes();
            let _ = d.swap_bytes();
        }

        fn test_wrong(x: u32) {
            let s = x.swap_bytes();
            assert(s == x); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
