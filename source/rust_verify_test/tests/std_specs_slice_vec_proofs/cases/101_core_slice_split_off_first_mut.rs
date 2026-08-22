#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_off_first_mut
// Source: core/src/slice/mod.rs:5035-5041
// Source item sha256: bd916b533cd3fed622062b911bb1ad18889d4240f66d45311415d0673e52c374
// Dependency manifest: proof_manifests/101_core_slice_split_off_first_mut/dependency_assumption_manifest.json

use core::mem::swap;
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

pub const fn split_off_first_mut<'a, T>(slice_ref: &mut &'a mut [T]) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_first_result::<T>(
                (*old(slice_ref))@,
                (*final(slice_ref))@,
                *ret.unwrap(),
            )
            && (seq![*final(ret.unwrap())] + (*final(slice_ref))@).len()
                == (*old(slice_ref))@.len(),
{
    let ghost source = (*slice_ref)@;
    let mut replacement: &'a mut [T] = &mut [];
    swap(slice_ref, &mut replacement);
    let slice = replacement;

    if slice.len() != 0 {
        proof {
            assert(slice@ == source);
        }
        let ghost replaced = slice@;
        let (head, rem) = slice.split_at_mut(1);
        proof {
            replaced.lemma_split_at(1);
            assert(head@ =~= replaced.subrange(0, 1));
            assert(rem@ =~= replaced.subrange(1, replaced.len() as int));
            assert(head@[0] == replaced[0]);
            assert(replaced == source);
        }
        let ghost remaining = rem@;
        let first = &mut head[0];
        proof {
            assert(*first == source[0]);
            assert(remaining == source.subrange(1, source.len() as int));
        }
        *slice_ref = rem;
        proof {
            assert((*slice_ref)@ == remaining);
            assert(slice_split_off_first_result::<T>(source, (*slice_ref)@, *first));
            assert((seq![*first] + (*slice_ref)@).len() == source.len());
        }
        Some(first)
    } else {
        proof {
            assert(slice@ == source);
            assert(source.len() == 0);
            assert((*slice_ref)@ =~= source);
        }
        None
    }
}

}
