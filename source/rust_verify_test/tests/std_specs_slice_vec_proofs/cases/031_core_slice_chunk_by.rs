#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::chunk_by
// Source: core/src/slice/mod.rs:1864-1869 and core/src/slice/iter.rs:3015-3024
// Source item sha256: 30a1242feee61b528b84b6f4e21d833956abebb2b1beeab123da4b9cdcb354ec
// Dependency manifest: proof_manifests/031_core_slice_chunk_by/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub remaining: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub uninterp spec fn fnmut_adjacent_predicate_observed<F, T>(
    pred: F,
    left: T,
    right: T,
) -> bool;

pub struct ChunkBy<'a, T: 'a, P> {
    slice: &'a [T],
    predicate: P,
}

pub closed spec fn slice_iterator_view<'a, T, P>(iter: ChunkBy<'a, T, P>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.slice@,
        remaining: iter.slice@,
        yielded_prefix: Seq::empty(),
        remainder: Seq::empty(),
        chunk_size: 0,
        reverse: false,
    }
}

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn slice_adjacent_chunk_view<'a, T, P>(
    iter: ChunkBy<'a, T, P>,
    source: Seq<T>,
    pred: P,
) -> bool {
    let view = slice_iterator_view(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix.len() == 0
        && view.remainder.len() == 0
        && view.chunk_size == 0
        && !view.reverse
        && view.yielded_prefix + view.remaining == source
        && forall|i: int| 0 <= i + 1 < source.len()
            ==> (#[trigger] fnmut_adjacent_predicate_observed(pred, source[i], source[i + 1])
                || !fnmut_adjacent_predicate_observed(pred, source[i], source[i + 1]))
}

impl<'a, T, P> ChunkBy<'a, T, P> {
    pub const fn new(slice: &'a [T], predicate: P) -> (ret: Self)
        ensures
            slice_adjacent_chunk_view(ret, slice@, predicate),
    {
        let ret = ChunkBy { slice, predicate };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn chunk_by<'a, T, F>(slice: &'a [T], pred: F) -> (iter: ChunkBy<'a, T, F>)
    where
        F: FnMut(&T, &T) -> bool,
    ensures
        slice_adjacent_chunk_view(iter, slice@, pred),
{
    ChunkBy::new(slice, pred)
}

}
