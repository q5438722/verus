#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_first
// Source: core/src/slice/mod.rs:198-200
// Source item sha256: c8c87480788024ae6b8f7abc667e8911dcb4430f989b2cb4900c3bac6257f65b
// Dependency manifest: proof_manifests/088_core_slice_split_first/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

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

}
