#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::rchunks
// Source: core/src/slice/mod.rs:1686-1689 and core/src/slice/iter.rs:2311-2320
// Source item sha256: b9b3dcbff1d8e2bf876c0c0525c3ba2b65d44b886640c210c255b801e83d00d5
// Dependency manifest: proof_manifests/066_core_slice_rchunks/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remaining: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct RChunks<'a, T: 'a> {
    v: &'a [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: RChunks<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: Seq::empty(),
        chunk_size: iter.chunk_size as int,
        reverse: true,
    }
}

impl<'a, T> RChunks<'a, T> {
    pub const fn new(slice: &'a [T], size: usize) -> (ret: Self)
        ensures
            slice_iterator_view(ret).source == slice@,
            slice_iterator_view(ret).remaining == slice@,
            slice_iterator_view(ret).yielded_prefix == Seq::empty(),
            slice_iterator_view(ret).remainder == Seq::empty(),
            slice_iterator_view(ret).chunk_size == size as int,
            slice_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice, chunk_size: size };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn rchunks<'a, T>(slice: &'a [T], chunk_size: usize) -> (iter: RChunks<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).remaining == slice@,
        slice_iterator_view(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view(iter).remainder == Seq::empty(),
        slice_iterator_view(iter).chunk_size == chunk_size as int,
        slice_iterator_view(iter).reverse,
{
    assert(chunk_size != 0);
    RChunks::new(slice, chunk_size)
}

}
