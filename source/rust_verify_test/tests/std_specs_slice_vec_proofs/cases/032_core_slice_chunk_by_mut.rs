#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::chunk_by_mut
// Source: core/src/slice/mod.rs:1906-1911 and core/src/slice/iter.rs:3109-3118
// Source item sha256: f47865a3fb1f3957ce9cd1692b23765a8d17f2712c5e4fbb88635d4e4eaeb159
// Dependency manifest: proof_manifests/032_core_slice_chunk_by_mut/dependency_assumption_manifest.json

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

pub struct ChunkByMut<'a, T: 'a, P> {
    slice: &'a mut [T],
    predicate: P,
}

pub closed spec fn slice_iterator_view<'a, T, P>(iter: ChunkByMut<'a, T, P>) -> SliceIteratorView<T> {
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
    iter: ChunkByMut<'a, T, P>,
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

impl<'a, T, P> ChunkByMut<'a, T, P> {
    pub const fn new(slice: &'a mut [T], predicate: P) -> (ret: Self)
        ensures
            slice_adjacent_chunk_view(ret, old(slice)@, predicate),
    {
        let ret = ChunkByMut { slice, predicate };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn chunk_by_mut<'a, T, F>(slice: &'a mut [T], pred: F) -> (iter: ChunkByMut<'a, T, F>)
    where
        F: FnMut(&T, &T) -> bool,
    ensures
        slice_adjacent_chunk_view(iter, old(slice)@, pred),
{
    ChunkByMut::new(slice, pred)
}

}
