#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::array_windows
// Source: core/src/slice/mod.rs:1646-1649 and core/src/slice/iter.rs:2181-2189
// Source item sha256: cb847876b5acfbc5b4dc0965b2f5e056bdd76de3517d4dc348c0f54d3d28bd54
// Dependency manifest: proof_manifests/010_core_slice_array_windows/dependency_assumption_manifest.json

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

pub struct ArrayWindows<'a, T: 'a, const N: usize> {
    v: &'a [T],
}

pub closed spec fn slice_iterator_view<'a, T, const N: usize>(
    iter: ArrayWindows<'a, T, N>,
) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: Seq::empty(),
        chunk_size: N as int,
        reverse: false,
    }
}

impl<'a, T, const N: usize> ArrayWindows<'a, T, N> {
    pub const fn new(slice: &'a [T]) -> (ret: Self)
        requires
            N != 0,
        ensures
            slice_iterator_view(ret).source == slice@,
            slice_iterator_view(ret).remaining == slice@,
            slice_iterator_view(ret).yielded_prefix.len() == 0,
            slice_iterator_view(ret).remainder.len() == 0,
            slice_iterator_view(ret).chunk_size == N as int,
            !slice_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn array_windows<'a, T, const N: usize>(slice: &'a [T]) -> (iter: ArrayWindows<'a, T, N>)
    requires
        N != 0,
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).remaining == slice@,
        slice_iterator_view(iter).yielded_prefix.len() == 0,
        slice_iterator_view(iter).remainder.len() == 0,
        slice_iterator_view(iter).chunk_size == N as int,
        !slice_iterator_view(iter).reverse,
{
    assert(N != 0);
    ArrayWindows::new(slice)
}

}
