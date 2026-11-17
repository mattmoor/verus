#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] duration_construct_and_read verus_code! {
        use vstd::prelude::*;
        use core::time::Duration;

        fn test_from_secs(s: u64) {
            let d = Duration::from_secs(s);
            assert(d.as_secs() == s);
            assert(d.subsec_nanos() == 0);
            let n = d.as_nanos();
            assert(n == s * 1_000_000_000);
        }

        fn test_from_millis() {
            let d = Duration::from_millis(2_500);
            let s = d.as_secs();
            let n = d.subsec_nanos();
            let m = d.subsec_millis();
            let u = d.subsec_micros();
            assert(s == 2);
            assert(n == 500_000_000);
            assert(m == 500);
            assert(u == 500_000);
            let total = d.as_millis();
            assert(total == 2_500);
        }

        fn test_from_micros_nanos() {
            let a = Duration::from_micros(1_000_001);
            assert(a.as_secs() == 1);
            assert(a.subsec_nanos() == 1_000);
            assert(a.as_micros() == 1_000_001);
            let b = Duration::from_nanos(3_000_000_007);
            assert(b.as_secs() == 3);
            assert(b.subsec_nanos() == 7);
        }

        fn test_new_carries() {
            let d = Duration::new(1, 2_000_000_001);
            assert(d.as_secs() == 3);
            assert(d.subsec_nanos() == 1);
        }

        fn test_new_generic(s: u64, n: u32)
            requires
                s < u64::MAX,
                n < 1_000_000_000,
        {
            let d = Duration::new(s, n);
            assert(d.as_secs() == s);
            assert(d.subsec_nanos() == n);
        }

        fn test_nanos_bound(d: Duration) {
            let n = d.subsec_nanos();
            assert(n < 1_000_000_000);
            let m = d.subsec_millis();
            assert(m < 1_000);
        }

        fn test_equal_views() {
            let a = Duration::from_secs(1);
            let b = Duration::from_millis(1_000);
            assert(a@ == b@);
            assert(a == b);
        }

        // SQLite-style: a timeout in milliseconds as whole seconds plus the rest.
        fn split_ms(ms: u64) -> (r: (u64, u32))
            ensures
                r.0 == ms / 1_000,
                r.1 == (ms % 1_000) * 1_000_000,
        {
            let d = Duration::from_millis(ms);
            (d.as_secs(), d.subsec_nanos())
        }

        spec fn spec_secs(d: Duration) -> u64 {
            d.as_secs()
        }

        proof fn test_spec(d: Duration) {
            assert(spec_secs(d) == d@.0);
        }

        fn test_no_unwind(s: u64, d: Duration)
            no_unwind
        {
            let _ = Duration::from_secs(s);
            let _ = Duration::from_millis(s);
            let _ = d.as_secs();
            let _ = d.subsec_nanos();
            let _ = d.as_millis();
        }

        fn test_wrong() {
            let d = Duration::from_millis(1_500);
            assert(d.as_secs() == 2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] duration_checked_arith verus_code! {
        use vstd::prelude::*;
        use core::time::Duration;

        fn test_add() {
            let a = Duration::from_millis(1_600);
            let b = Duration::from_millis(1_600);
            let c = a.checked_add(b);
            match c {
                Some(d) => {
                    assert(d.as_secs() == 3);
                    assert(d.subsec_millis() == 200);
                }
                None => {
                    assert(false);
                }
            }
        }

        fn test_add_overflow() {
            let a = Duration::new(u64::MAX, 999_999_999);
            let b = Duration::from_nanos(1);
            let c = a.checked_add(b);
            assert(c is None);
        }

        fn test_sub() {
            let a = Duration::from_secs(2);
            let b = Duration::from_millis(500);
            let c = a.checked_sub(b);
            assert(c is Some);
            let d = c.unwrap();
            assert(d.as_millis() == 1_500);
            let e = b.checked_sub(a);
            assert(e is None);
        }

        fn test_new_overflow_fails() {
            let d = Duration::new(u64::MAX, 1_000_000_000); // FAILS
        }

        fn test_wrong(a: Duration, b: Duration) {
            let c = a.checked_sub(b);
            assert(c is Some); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}
