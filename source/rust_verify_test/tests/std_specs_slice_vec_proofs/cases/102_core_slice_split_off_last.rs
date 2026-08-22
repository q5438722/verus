#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_off_last
// Source: core/src/slice/mod.rs:5060-5065
// Source item sha256: 0fcd04a4daac54f0807cbce4e95f3ec9103d5c33d680b81d2ffba339eac4e41e
// Dependency manifest: proof_manifests/102_core_slice_split_off_last/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn slice_split_off_last_result<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    value: T,
) -> bool {
    source.len() != 0
        && value == source[(source.len() - 1) as int]
        && remaining == source.subrange(0, (source.len() - 1) as int)
}

pub const fn split_last<'a, T>(slice: &'a [T]) -> (ret: Option<(&'a T, &'a [T])>)
    ensures
        slice@.len() == 0 ==> ret.is_none(),
        slice@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == slice@[(slice@.len() - 1) as int]
            && ret.unwrap().1@ == slice@.subrange(0, (slice@.len() - 1) as int),
{
    if slice.len() != 0 {
        let split = slice.len() - 1;
        let (init, tail) = slice.split_at(split);
        proof {
            assert(split as int == slice@.len() - 1);
            slice@.lemma_split_at(split as int);
            assert(init@ =~= slice@.subrange(0, split as int));
            assert(tail@ =~= slice@.subrange(split as int, slice@.len() as int));
            assert(tail@.len() == 1);
            assert(tail@[0] == slice@[(slice@.len() - 1) as int]);
        }
        let last = &tail[0];
        proof {
            assert(*last == tail@[0]);
        }
        Some((last, init))
    } else {
        None
    }
}

pub const fn split_off_last<'a, T>(slice_ref: &mut &'a [T]) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_last_result::<T>(
                (*old(slice_ref))@,
                (*final(slice_ref))@,
                *ret.unwrap(),
            ),
{
    let ghost source = (*slice_ref)@;
    let split = split_last(*slice_ref);
    match split {
        None => {
            proof {
                assert(source.len() == 0);
                assert((*slice_ref)@ == source);
            }
            None
        },
        Some((last, rem)) => {
            proof {
                assert(source.len() != 0);
                assert(*last == source[(source.len() - 1) as int]);
                assert(rem@ == source.subrange(0, (source.len() - 1) as int));
            }
            *slice_ref = rem;
            proof {
                assert((*slice_ref)@ == rem@);
                assert(slice_split_off_last_result::<T>(source, (*slice_ref)@, *last));
            }
            Some(last)
        },
    }
}

}
