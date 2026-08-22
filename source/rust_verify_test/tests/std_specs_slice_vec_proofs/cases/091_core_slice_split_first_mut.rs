#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_first_mut
// Source: core/src/slice/mod.rs:220-222
// Source item sha256: 8d6d5b36d373d9e4556d437c6945a36066ed634bd2931a95cbb07d5197b5c3b4
// Dependency manifest: proof_manifests/091_core_slice_split_first_mut/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub const fn split_first_mut<'a, T>(slice: &'a mut [T]) -> (ret: Option<(&'a mut T, &'a mut [T])>)
    ensures
        old(slice)@.len() == 0 ==> ret.is_none() && final(slice)@ == old(slice)@,
        old(slice)@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == old(slice)@[0]
            && ret.unwrap().1@ == old(slice)@.subrange(1, old(slice)@.len() as int)
            && final(slice)@ == seq![*final(ret.unwrap().0)] + final(ret.unwrap().1)@,
{
    if slice.len() != 0 {
        let ghost source = slice@;
        let (head, tail) = slice.split_at_mut(1);
        proof {
            source.lemma_split_at(1);
            assert(head@ =~= source.subrange(0, 1));
            assert(tail@ =~= source.subrange(1, source.len() as int));
            assert(head@[0] == source[0]);
        }
        let first = &mut head[0];
        Some((first, tail))
    } else {
        None
    }
}

}
