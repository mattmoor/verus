#![allow(unused_imports)]
use super::super::arithmetic::div_mod::{rust_div, rust_rem};
use super::super::prelude::*;
use super::super::wrapping::*;

use core::cmp::Ordering;

verus! {

/// The smallest multiple of `y` that is `>= x` (for `y > 0`), matching the value
/// std's `next_multiple_of` / `checked_next_multiple_of` compute.
pub open spec fn next_multiple_of(x: int, y: int) -> int
    recommends
        y > 0,
{
    if x % y == 0 {
        x
    } else {
        x + (y - x % y)
    }
}

// The `uN_swap_bytes` fns below name byte `k` of `x` (counting from the least significant)
// `bk` and move it to byte `N - 1 - k`. Each byte is masked before it is shifted left, so
// no intermediate value leaves the type's range, and the definitions evaluate with
// `by (compute)` as well as `by (bit_vector)`.
/// `x.swap_bytes()`: the bytes of `x` in reverse order.
pub open spec fn u8_swap_bytes(x: u8) -> u8 {
    x
}

/// `x.swap_bytes()`: the bytes of `x` in reverse order.
pub open spec fn u16_swap_bytes(x: u16) -> u16 {
    let b0 = x & 0xff;
    let b1 = (x >> 8u32) & 0xff;
    (b0 << 8u32) | b1
}

/// `x.swap_bytes()`: the bytes of `x` in reverse order.
pub open spec fn u32_swap_bytes(x: u32) -> u32 {
    let b0 = x & 0xff;
    let b1 = (x >> 8u32) & 0xff;
    let b2 = (x >> 16u32) & 0xff;
    let b3 = (x >> 24u32) & 0xff;
    (b0 << 24u32) | (b1 << 16u32) | (b2 << 8u32) | b3
}

/// `x.swap_bytes()`: the bytes of `x` in reverse order.
pub open spec fn u64_swap_bytes(x: u64) -> u64 {
    let b0 = x & 0xff;
    let b1 = (x >> 8u32) & 0xff;
    let b2 = (x >> 16u32) & 0xff;
    let b3 = (x >> 24u32) & 0xff;
    let b4 = (x >> 32u32) & 0xff;
    let b5 = (x >> 40u32) & 0xff;
    let b6 = (x >> 48u32) & 0xff;
    let b7 = (x >> 56u32) & 0xff;
    (b0 << 56u32) | (b1 << 48u32) | (b2 << 40u32) | (b3 << 32u32) | (b4 << 24u32) | (b5 << 16u32)
        | (b6 << 8u32) | b7
}

/// `x.swap_bytes()`: the bytes of `x` in reverse order.
pub open spec fn u128_swap_bytes(x: u128) -> u128 {
    let b0 = x & 0xff;
    let b1 = (x >> 8u32) & 0xff;
    let b2 = (x >> 16u32) & 0xff;
    let b3 = (x >> 24u32) & 0xff;
    let b4 = (x >> 32u32) & 0xff;
    let b5 = (x >> 40u32) & 0xff;
    let b6 = (x >> 48u32) & 0xff;
    let b7 = (x >> 56u32) & 0xff;
    let b8 = (x >> 64u32) & 0xff;
    let b9 = (x >> 72u32) & 0xff;
    let b10 = (x >> 80u32) & 0xff;
    let b11 = (x >> 88u32) & 0xff;
    let b12 = (x >> 96u32) & 0xff;
    let b13 = (x >> 104u32) & 0xff;
    let b14 = (x >> 112u32) & 0xff;
    let b15 = (x >> 120u32) & 0xff;
    (b0 << 120u32) | (b1 << 112u32) | (b2 << 104u32) | (b3 << 96u32) | (b4 << 88u32) | (b5 << 80u32)
        | (b6 << 72u32) | (b7 << 64u32) | (b8 << 56u32) | (b9 << 48u32) | (b10 << 40u32) | (b11
        << 32u32) | (b12 << 24u32) | (b13 << 16u32) | (b14 << 8u32) | b15
}

/// `x.swap_bytes()`: the bytes of `x` in reverse order, at the width of `usize`.
pub open spec fn usize_swap_bytes(x: usize) -> usize {
    let b0 = x & 0xff;
    let b1 = (x >> 8u32) & 0xff;
    let b2 = (x >> 16u32) & 0xff;
    let b3 = (x >> 24u32) & 0xff;
    if usize::BITS == 32 {
        (b0 << 24u32) | (b1 << 16u32) | (b2 << 8u32) | b3
    } else {
        let b4 = (x >> 32u32) & 0xff;
        let b5 = (x >> 40u32) & 0xff;
        let b6 = (x >> 48u32) & 0xff;
        let b7 = (x >> 56u32) & 0xff;
        (b0 << 56u32) | (b1 << 48u32) | (b2 << 40u32) | (b3 << 32u32) | (b4 << 24u32) | (b5
            << 16u32) | (b6 << 8u32) | b7
    }
}

} // verus!
macro_rules! num_specs {
    ($uN: ty, $iN: ty, $mod_u_tmp:ident, $mod_i_tmp:ident, $mod_u:ident, $mod_i:ident, $range:expr) => {
        verus! {

        // Unsigned ints (u8, u16, etc.)

        // Put in separate module to avoid name collisions.
        // Names don't matter - the user uses the stdlib functions.
        mod $mod_u_tmp {
            use super::*;

            pub assume_specification[<$uN as Clone>::clone](x: &$uN) -> (res: $uN)
                ensures res == x;

            impl super::super::cmp::PartialEqSpecImpl for $uN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$uN) -> bool {
                    *self == *other
                }
            }

            impl super::super::cmp::PartialOrdSpecImpl for $uN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$uN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            impl super::super::cmp::OrdSpecImpl for $uN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$uN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$uN as PartialEq<$uN>>::eq](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialEq<$uN>>::ne](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as Ord>::cmp](x: &$uN, y: &$uN) -> Ordering;

            pub assume_specification[<$uN as PartialOrd<$uN>>::partial_cmp](x: &$uN, y: &$uN) -> Option<Ordering>;

            pub assume_specification[<$uN as PartialOrd<$uN>>::lt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::le](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::gt](x: &$uN, y: &$uN) -> bool;

            pub assume_specification[<$uN as PartialOrd<$uN>>::ge](x: &$uN, y: &$uN) -> bool;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_add](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_add(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_add_signed](x: $uN, y: $iN) -> $uN
                returns $mod_u::wrapping_add_signed(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_sub](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_sub(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_mul](x: $uN, y: $uN) -> $uN
                returns $mod_u::wrapping_mul(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_shl](x: $uN, rhs: u32) -> $uN
                returns $mod_u::wrapping_shl(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::wrapping_shr](x: $uN, rhs: u32) -> $uN
                returns $mod_u::wrapping_shr(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_add](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_add_signed](x: $uN, y: $iN) -> Option<$uN>
                returns (
                    if x + y > <$uN>::MAX || x + y < 0 {
                        None
                    } else {
                        Some((x + y) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_sub](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x - y < 0 {
                        None
                    } else {
                        Some((x - y) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_mul](x: $uN, y: $uN) -> Option<$uN>
                returns (
                    if x * y > <$uN>::MAX {
                        None
                    } else {
                        Some((x * y) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_next_multiple_of](x: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    } else if next_multiple_of(x as int, rhs as int) > <$uN>::MAX {
                        None
                    } else {
                        Some(next_multiple_of(x as int, rhs as int) as $uN)
                    }
                )
                no_unwind;

            pub open spec fn checked_div(x: $uN, y: $uN) -> Option<$uN> {
                if y == 0 {
                    None
                } else {
                    Some(x / y)
                }
            }

            #[verifier::when_used_as_spec(checked_div)]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_div](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    result == checked_div(lhs, rhs),
                no_unwind;

            #[verifier::when_used_as_spec(checked_div)]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_div_euclid](lhs: $uN, rhs: $uN) -> (result: Option<$uN>)
                ensures
                    // checked_div is the same as checked_div_euclid for unsigned ints
                    result == checked_div(lhs, rhs),
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_rem](lhs: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    }
                    else {
                        Some((lhs % rhs) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::checked_rem_euclid](lhs: $uN, rhs: $uN) -> Option<$uN>
                returns (
                    if rhs == 0 {
                        None
                    }
                    else {
                        Some((lhs % rhs) as $uN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::saturating_add](x: $uN, y: $uN) -> $uN
                returns (
                    if x + y > <$uN>::MAX {
                        <$uN>::MAX
                    } else {
                        (x + y) as $uN
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::saturating_sub](x: $uN, y: $uN) -> $uN
                returns (
                    if x - y < <$uN>::MIN {
                        <$uN>::MIN
                    } else {
                        (x - y) as $uN
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::saturating_mul](x: $uN, y: $uN) -> $uN
                returns (
                    if x * y > <$uN>::MAX {
                        <$uN>::MAX
                    } else {
                        (x * y) as $uN
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::is_multiple_of](x: $uN, y: $uN) -> bool
                returns (
                    if y == 0 { x == 0 } else { x % y == 0 }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::div_ceil](lhs: $uN, rhs: $uN) -> $uN
                requires rhs != 0,
                returns (
                    if lhs % rhs == 0 {
                        lhs / rhs
                    } else {
                        (lhs / rhs + 1) as $uN
                    }
                )
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::abs_diff](x: $uN, y: $uN) -> $uN
                returns (
                    if x < y {
                        (y - x) as $uN
                    } else {
                        (x - y) as $uN
                    }
                )
                opens_invariants none
                no_unwind;
        }

        // Signed ints (i8, i16, etc.)

        mod $mod_i_tmp {
            use super::*;

            pub assume_specification[<$iN as Clone>::clone](x: &$iN) -> (res: $iN)
                ensures res == x;

            impl super::super::cmp::PartialEqSpecImpl for $iN {
                open spec fn obeys_eq_spec() -> bool {
                    true
                }

                open spec fn eq_spec(&self, other: &$iN) -> bool {
                    *self == *other
                }
            }

            impl super::super::cmp::PartialOrdSpecImpl for $iN {
                open spec fn obeys_partial_cmp_spec() -> bool {
                    true
                }

                open spec fn partial_cmp_spec(&self, other: &$iN) -> Option<Ordering> {
                    if *self < *other {
                        Some(Ordering::Less)
                    } else if *self > *other {
                        Some(Ordering::Greater)
                    } else {
                        Some(Ordering::Equal)
                    }
                }
            }

            impl super::super::cmp::OrdSpecImpl for $iN {
                open spec fn obeys_cmp_spec() -> bool {
                    true
                }

                open spec fn cmp_spec(&self, other: &$iN) -> Ordering {
                    if *self < *other {
                        Ordering::Less
                    } else if *self > *other {
                        Ordering::Greater
                    } else {
                        Ordering::Equal
                    }
                }
            }

            pub assume_specification[<$iN as PartialEq<$iN>>::eq](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialEq<$iN>>::ne](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as Ord>::cmp](x: &$iN, y: &$iN) -> Ordering;

            pub assume_specification[<$iN as PartialOrd<$iN>>::partial_cmp](x: &$iN, y: &$iN) -> Option<Ordering>;

            pub assume_specification[<$iN as PartialOrd<$iN>>::lt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::le](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::gt](x: &$iN, y: &$iN) -> bool;

            pub assume_specification[<$iN as PartialOrd<$iN>>::ge](x: &$iN, y: &$iN) -> bool;

            // `MIN.abs()` overflows: it panics with overflow checks on and returns `MIN`
            // without them, so the spec requires `x != MIN` as `-x` would.
            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::abs](x: $iN) -> $iN
                requires x != <$iN>::MIN,
                returns (
                    if x < 0 {
                        -x
                    } else {
                        x as int
                    }
                ) as $iN
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::unsigned_abs](x: $iN) -> $uN
                returns (
                    if x < 0 {
                        -x
                    } else {
                        x as int
                    }
                ) as $uN
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::abs_diff](x: $iN, y: $iN) -> $uN
                returns (
                    if x < y {
                        y - x
                    } else {
                        x - y
                    }
                ) as $uN
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_add](x: $iN, y: $iN) -> $iN
                returns $mod_i::wrapping_add(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_add_unsigned](x: $iN, y: $uN) -> $iN
                returns $mod_i::wrapping_add_unsigned(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_sub](x: $iN, y: $iN) -> (res: $iN)
                returns $mod_i::wrapping_sub(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_mul](x: $iN, y: $iN) -> $iN
                returns $mod_i::wrapping_mul(x, y)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_shl](x: $iN, rhs: u32) -> $iN
                returns $mod_i::wrapping_shl(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::wrapping_shr](x: $iN, rhs: u32) -> $iN
                returns $mod_i::wrapping_shr(x, rhs)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_add](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX || x + y < <$iN>::MIN {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_add_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x + y > <$iN>::MAX {
                        None
                    } else {
                        Some((x + y) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_sub](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x - y > <$iN>::MAX || x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_sub_unsigned](x: $iN, y: $uN) -> Option<$iN>
                returns (
                    if x - y < <$iN>::MIN {
                        None
                    } else {
                        Some((x - y) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_mul](x: $iN, y: $iN) -> Option<$iN>
                returns (
                    if x * y > <$iN>::MAX || x * y < <$iN>::MIN {
                        None
                    } else {
                        Some((x * y) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_div](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some(rust_div(lhs as int, rhs as int) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_div_euclid](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some((lhs / rhs) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_rem](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some(rust_rem(lhs as int, rhs as int) as $iN)
                    }
                )
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::checked_rem_euclid](lhs: $iN, rhs: $iN) -> Option<$iN>
                returns (
                    if rhs == 0 || (lhs == <$iN>::MIN && rhs == -1) {
                        None
                    } else {
                        Some((lhs % rhs) as $iN)
                    }
                )
                no_unwind;
        }

        }
    };
}

num_specs!(u8, i8, u8_specs_tmp, i8_specs_tmp, u8_specs, i8_specs, 0x100);
num_specs!(u16, i16, u16_specs_tmp, i16_specs_tmp, u16_specs, i16_specs, 0x1_0000);
num_specs!(u32, i32, u32_specs_tmp, i32_specs_tmp, u32_specs, i32_specs, 0x1_0000_0000);
num_specs!(u64, i64, u64_specs_tmp, i64_specs_tmp, u64_specs, i64_specs, 0x1_0000_0000_0000_0000);
num_specs!(
    u128,
    i128,
    u128_specs_tmp,
    i128_specs_tmp,
    u128_specs,
    i128_specs,
    0x1_0000_0000_0000_0000_0000_0000_0000_0000
);
num_specs!(
    usize,
    isize,
    usize_specs_tmp,
    isize_specs_tmp,
    usize_specs,
    isize_specs,
    (usize::MAX - usize::MIN + 1)
);

macro_rules! swap_bytes_specs {
    ($uN: ty, $iN: ty, $mod_tmp:ident, $spec:ident) => {
        verus! {

        mod $mod_tmp {
            use super::*;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$uN>::swap_bytes](x: $uN) -> $uN
                returns $spec(x)
                opens_invariants none
                no_unwind;

            #[verifier::allow_in_spec]
            #[cfg(not(verus_verify_core))]
            pub assume_specification[<$iN>::swap_bytes](x: $iN) -> $iN
                returns $spec(x as $uN) as $iN
                opens_invariants none
                no_unwind;
        }

        }
    };
}

swap_bytes_specs!(u8, i8, u8_swap_bytes_tmp, u8_swap_bytes);
swap_bytes_specs!(u16, i16, u16_swap_bytes_tmp, u16_swap_bytes);
swap_bytes_specs!(u32, i32, u32_swap_bytes_tmp, u32_swap_bytes);
swap_bytes_specs!(u64, i64, u64_swap_bytes_tmp, u64_swap_bytes);
swap_bytes_specs!(u128, i128, u128_swap_bytes_tmp, u128_swap_bytes);
swap_bytes_specs!(usize, isize, usize_swap_bytes_tmp, usize_swap_bytes);
