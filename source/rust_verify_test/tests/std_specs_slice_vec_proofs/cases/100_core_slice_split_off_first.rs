#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_off_first
// Source: core/src/slice/mod.rs:5010-5015
// Source item sha256: b373389fae9235ca313dc0a9cad7598affe7f1e8a19b13af7334c7ea7affd93d
// Dependency manifest: proof_manifests/100_core_slice_split_off_first/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn slice_split_off_first_result<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    value: T,
) -> bool {
    source.len() != 0 && value == source[0] && remaining == source.subrange(1, source.len() as int)
}

pub const fn split_first<'a, T>(slice: &'a [T]) -> (ret: Option<(&'a T, &'a [T])>)
    ensures
        slice@.len() == 0 ==> ret.is_none(),
        slice@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == slice@[0]
            && ret.unwrap().1@ == slice@.subrange(1, slice@.len() as int),
{
    if slice.len() != 0 {
        let (head, tail) = slice.split_at(1);
        let first = &head[0];
        proof {
            slice@.lemma_split_at(1);
            assert(head@ =~= slice@.subrange(0, 1));
            assert(tail@ =~= slice@.subrange(1, slice@.len() as int));
            assert(*first == head@[0]);
            assert(head@[0] == slice@[0]);
        }
        Some((first, tail))
    } else {
        None
    }
}

pub const fn split_off_first<'a, T>(slice_ref: &mut &'a [T]) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_first_result::<T>(
                (*old(slice_ref))@,
                (*final(slice_ref))@,
                *ret.unwrap(),
            ),
{
    let ghost source = (*slice_ref)@;
    let split = split_first(*slice_ref);
    match split {
        None => {
            proof {
                assert(source.len() == 0);
                assert((*slice_ref)@ == source);
            }
            None
        },
        Some((first, rem)) => {
            proof {
                assert(source.len() != 0);
                assert(*first == source[0]);
                assert(rem@ == source.subrange(1, source.len() as int));
            }
            *slice_ref = rem;
            proof {
                assert((*slice_ref)@ == rem@);
                assert(slice_split_off_first_result::<T>(source, (*slice_ref)@, *first));
            }
            Some(first)
        },
    }
}

}
