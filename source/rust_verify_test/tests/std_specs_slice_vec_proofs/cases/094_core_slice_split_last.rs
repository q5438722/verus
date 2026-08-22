#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_last
// Source: core/src/slice/mod.rs:240-242
// Source item sha256: 494ab97059b11f5875c876637025f3dd9db9d65354600d4e1769556847dac13a
// Dependency manifest: proof_manifests/094_core_slice_split_last/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

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

}
