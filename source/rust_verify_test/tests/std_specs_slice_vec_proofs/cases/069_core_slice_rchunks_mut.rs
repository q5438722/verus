#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::rchunks_mut
// Source: core/src/slice/mod.rs:1730-1733 and core/src/slice/iter.rs:2471-2487
// Source item sha256: d910a481ba713ebe6456eb7bd6f6fb02a50cb5e7fc88d652ee0d88ee9082632c
// Dependency manifest: proof_manifests/069_core_slice_rchunks_mut/dependency_assumption_manifest.json

use core::marker::PhantomData;
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

pub struct RChunksMut<'a, T: 'a> {
    v: &'a mut [T],
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: RChunksMut<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: Seq::empty(),
        chunk_size: iter.chunk_size as int,
        reverse: true,
    }
}

impl<'a, T> RChunksMut<'a, T> {
    pub const fn new(slice: &'a mut [T], size: usize) -> (ret: Self)
        ensures
            slice_iterator_view(ret).source == old(slice)@,
            slice_iterator_view(ret).remaining == old(slice)@,
            slice_iterator_view(ret).yielded_prefix == Seq::empty(),
            slice_iterator_view(ret).remainder == Seq::empty(),
            slice_iterator_view(ret).chunk_size == size as int,
            slice_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice, chunk_size: size, _marker: PhantomData };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn rchunks_mut<'a, T>(slice: &'a mut [T], chunk_size: usize) -> (iter: RChunksMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view(iter).source == old(slice)@,
        slice_iterator_view(iter).remaining == old(slice)@,
        slice_iterator_view(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view(iter).remainder == Seq::empty(),
        slice_iterator_view(iter).chunk_size == chunk_size as int,
        slice_iterator_view(iter).reverse,
{
    assert(chunk_size != 0);
    RChunksMut::new(slice, chunk_size)
}

}
