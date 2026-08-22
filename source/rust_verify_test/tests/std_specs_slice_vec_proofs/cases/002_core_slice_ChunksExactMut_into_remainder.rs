#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::ChunksExactMut::into_remainder
// Source: core/src/slice/iter.rs:2013-2043
// Source item sha256: 594db173f21195a95d202ec519cecc6af52d53e18b1679cc8e143345cd85d1a9
// Dependency manifest: proof_manifests/002_core_slice_ChunksExactMut_into_remainder/dependency_assumption_manifest.json

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

pub struct ChunksExactMut<'a, T: 'a> {
    v: *mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: ChunksExactMut<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.rem@,
        yielded_prefix: Seq::empty(),
        remaining: Seq::empty(),
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: false,
    }
}

impl<'a, T> ChunksExactMut<'a, T> {
    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool {
        (self.rem@.len() as int) < self.chunk_size as int
    }

    pub fn into_remainder(self) -> (ret: &'a mut [T])
        ensures
            ret@ == slice_iterator_view(self).remainder,
            ret@.len() < slice_iterator_view(self).chunk_size,
    {
        proof {
            reveal(slice_iterator_view);
            use_type_invariant(&self);
        }
        let Self { v: _, rem, chunk_size: _, _marker: _ } = self;
        rem
    }
}

}
