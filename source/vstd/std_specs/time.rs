//! Specifications for `core::time::Duration`.
//!
//! A `Duration` is viewed as the pair `(secs, nanos)` of its whole seconds and the
//! nanoseconds below one second, the two fields std keeps. `nanos` is always below
//! `NANOS_PER_SEC`, so each length of time has exactly one view.
use super::super::prelude::*;
use core::time::Duration;

verus! {

pub const NANOS_PER_SEC: u32 = 1_000_000_000;

impl View for Duration {
    type V = (u64, u32);

    uninterp spec fn view(&self) -> (u64, u32);
}

/// The length of `d` in nanoseconds.
pub open spec fn duration_total_nanos(d: Duration) -> nat {
    d@.0 as nat * NANOS_PER_SEC as nat + d@.1 as nat
}

/// The `Duration` of `total` nanoseconds, split into whole seconds and the rest.
pub open spec fn duration_view_of_nanos(total: nat) -> (u64, u32) {
    ((total / NANOS_PER_SEC as nat) as u64, (total % NANOS_PER_SEC as nat) as u32)
}

/// The `Duration` whose view is `v`. With the axioms below, it makes `d@` injective.
pub uninterp spec fn duration_from_view(v: (u64, u32)) -> Duration;

pub broadcast axiom fn axiom_duration_nanos_bound(d: Duration)
    ensures
        (#[trigger] d@).1 < NANOS_PER_SEC,
;

pub broadcast axiom fn axiom_duration_from_view_view(d: Duration)
    ensures
        duration_from_view(#[trigger] d@) == d,
;

pub broadcast axiom fn axiom_duration_view_from_view(v: (u64, u32))
    requires
        v.1 < NANOS_PER_SEC,
    ensures
        #[trigger] duration_from_view(v)@ == v,
;

pub broadcast group group_duration_axioms {
    axiom_duration_nanos_bound,
    axiom_duration_from_view_view,
    axiom_duration_view_from_view,
}

// `Duration::new` carries whole seconds out of `nanos`, and panics if that overflows the
// seconds.
pub assume_specification[ Duration::new ](secs: u64, nanos: u32) -> (d: Duration)
    requires
        secs + nanos / NANOS_PER_SEC <= u64::MAX,
    ensures
        d@ == duration_view_of_nanos(secs as nat * NANOS_PER_SEC as nat + nanos as nat),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::from_secs ](secs: u64) -> (d: Duration)
    ensures
        d@ == (secs, 0u32),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::from_millis ](millis: u64) -> (d: Duration)
    ensures
        d@ == duration_view_of_nanos(millis as nat * 1_000_000),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::from_micros ](micros: u64) -> (d: Duration)
    ensures
        d@ == duration_view_of_nanos(micros as nat * 1_000),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::from_nanos ](nanos: u64) -> (d: Duration)
    ensures
        d@ == duration_view_of_nanos(nanos as nat),
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::as_secs ](d: &Duration) -> u64
    returns
        d@.0,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::subsec_nanos ](d: &Duration) -> u32
    returns
        d@.1,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::subsec_micros ](d: &Duration) -> u32
    returns
        d@.1 / 1_000,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::subsec_millis ](d: &Duration) -> u32
    returns
        d@.1 / 1_000_000,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::as_nanos ](d: &Duration) -> u128
    returns
        duration_total_nanos(*d) as u128,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::as_micros ](d: &Duration) -> u128
    returns
        (duration_total_nanos(*d) / 1_000) as u128,
    opens_invariants none
    no_unwind
;

#[verifier::allow_in_spec]
pub assume_specification[ Duration::as_millis ](d: &Duration) -> u128
    returns
        (duration_total_nanos(*d) / 1_000_000) as u128,
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::checked_add ](a: Duration, b: Duration) -> (r: Option<Duration>)
    ensures
        ({
            let total = duration_total_nanos(a) + duration_total_nanos(b);
            match r {
                Some(d) => {
                    &&& total / NANOS_PER_SEC as nat <= u64::MAX
                    &&& d@ == duration_view_of_nanos(total)
                },
                None => total / NANOS_PER_SEC as nat > u64::MAX,
            }
        }),
    opens_invariants none
    no_unwind
;

pub assume_specification[ Duration::checked_sub ](a: Duration, b: Duration) -> (r: Option<Duration>)
    ensures
        ({
            let (ta, tb) = (duration_total_nanos(a), duration_total_nanos(b));
            match r {
                Some(d) => {
                    &&& tb <= ta
                    &&& d@ == duration_view_of_nanos((ta - tb) as nat)
                },
                None => ta < tb,
            }
        }),
    opens_invariants none
    no_unwind
;

} // verus!
