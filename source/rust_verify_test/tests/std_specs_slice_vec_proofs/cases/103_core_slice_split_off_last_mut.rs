#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_off_last_mut
// Source: core/src/slice/mod.rs:5085-5091
// Source item sha256: 8a7346f07fcf4cf6ee992be7812103b22dbed089118e0b60902114b2f63cf6aa
// Dependency manifest: proof_manifests/103_core_slice_split_off_last_mut/dependency_assumption_manifest.json

use core::mem::swap;
use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn slice_split_off_last_result<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    value: T,
) -> bool {
    source.len() != 0
        && value == source[source.len() - 1]
        && remaining == source.subrange(0, source.len() - 1)
}

pub const fn split_off_last_mut<'a, T>(slice_ref: &mut &'a mut [T]) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_last_result::<T>(
                (*old(slice_ref))@,
                (*final(slice_ref))@,
                *ret.unwrap(),
            )
            && ((*final(slice_ref))@ + seq![*final(ret.unwrap())]).len()
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
        let split = slice.len() - 1;
        let (rem, tail) = slice.split_at_mut(split);
        proof {
            assert(split as int == replaced.len() - 1);
            replaced.lemma_split_at(split as int);
            assert(rem@ =~= replaced.subrange(0, split as int));
            assert(tail@ =~= replaced.subrange(split as int, replaced.len() as int));
            assert(tail@.len() == 1);
            assert(tail@[0] == replaced[replaced.len() - 1]);
            assert(replaced == source);
        }
        let ghost remaining = rem@;
        let last = &mut tail[0];
        proof {
            assert(*last == source[source.len() - 1]);
            assert(remaining == source.subrange(0, source.len() - 1));
        }
        *slice_ref = rem;
        proof {
            assert((*slice_ref)@ == remaining);
            assert(slice_split_off_last_result::<T>(source, (*slice_ref)@, *last));
            assert(((*slice_ref)@ + seq![*last]).len() == source.len());
        }
        Some(last)
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
