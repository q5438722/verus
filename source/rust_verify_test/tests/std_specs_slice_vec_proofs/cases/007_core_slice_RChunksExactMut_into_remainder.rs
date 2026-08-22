#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::RChunksExactMut::into_remainder
// Source: core/src/slice/iter.rs:2830-2859
// Source item sha256: e7afc872b12681ba54e0b518edd5b9d8e252d1866cb7a1524c6ae801db1b9c1e
// Dependency manifest: proof_manifests/007_core_slice_RChunksExactMut_into_remainder/dependency_assumption_manifest.json

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

pub struct RChunksExactMut<'a, T: 'a> {
    v: *mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: RChunksExactMut<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.rem@,
        yielded_prefix: Seq::empty(),
        remaining: Seq::empty(),
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: true,
    }
}

impl<'a, T> RChunksExactMut<'a, T> {
    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool {
        (self.rem@.len() as int) < self.chunk_size as int
    }

    pub const fn into_remainder(self) -> (ret: &'a mut [T])
        ensures
            ret@ == slice_iterator_view(self).remainder,
            ret@.len() < slice_iterator_view(self).chunk_size,
    {
        proof {
            reveal(slice_iterator_view);
            use_type_invariant(&self);
        }
        let Self { v: _, rem, chunk_size: _ } = self;
        rem
    }
}

}
