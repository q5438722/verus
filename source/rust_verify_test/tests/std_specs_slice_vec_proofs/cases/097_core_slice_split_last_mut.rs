#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_last_mut
// Source: core/src/slice/mod.rs:262-264
// Source item sha256: bea57e99b1e178d9176ff0b1a6f78a83dafce93f1f7485844e6275ac07ab2005
// Dependency manifest: proof_manifests/097_core_slice_split_last_mut/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub const fn split_last_mut<'a, T>(slice: &'a mut [T]) -> (ret: Option<(&'a mut T, &'a mut [T])>)
    ensures
        old(slice)@.len() == 0 ==> ret.is_none() && final(slice)@ == old(slice)@,
        old(slice)@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == old(slice)@[(old(slice)@.len() - 1) as int]
            && ret.unwrap().1@ == old(slice)@.subrange(0, (old(slice)@.len() - 1) as int)
            && final(slice)@ == final(ret.unwrap().1)@ + seq![*final(ret.unwrap().0)],
{
    if slice.len() != 0 {
        let ghost source = slice@;
        let split = slice.len() - 1;
        let (init, tail) = slice.split_at_mut(split);
        proof {
            assert(split as int == source.len() - 1);
            source.lemma_split_at(split as int);
            assert(init@ =~= source.subrange(0, split as int));
            assert(tail@ =~= source.subrange(split as int, source.len() as int));
            assert(tail@.len() == 1);
            assert(tail@[0] == source[(source.len() - 1) as int]);
        }
        let last = &mut tail[0];
        Some((last, init))
    } else {
        None
    }
}

}
