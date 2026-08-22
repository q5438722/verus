#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::RChunksExact::remainder
// Source: core/src/slice/iter.rs:2653-2690
// Source item sha256: b6dbb4f20cac2706f157dad53b7470a370b2ce86d848a48f8368d84056071572
// Dependency manifest: proof_manifests/006_core_slice_RChunksExact_remainder/dependency_assumption_manifest.json

use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remaining: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct RChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: &RChunksExact<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.rem@ + iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: true,
    }
}

impl<'a, T> RChunksExact<'a, T> {
    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool {
        (self.rem@.len() as int) < self.chunk_size as int
    }

    fn new(slice: &'a [T], chunk_size: usize) -> (ret: Self)
        requires
            chunk_size != 0,
        ensures
            ret.chunk_size == chunk_size,
            (ret.rem@.len() as int) < ret.chunk_size as int,
    {
        let rem = slice.len() % chunk_size;
        proof {
            lemma_mod_decreases(slice.len() as nat, chunk_size as nat);
            assert(rem <= slice.len());
        }
        let (fst, snd) = slice.split_at(rem);
        proof {
            let n = slice.len() as int;
            let c = chunk_size as int;
            lemma_mod_division_less_than_divisor(n, c);
            assert((rem as int) < c);
            slice@.lemma_split_at(rem as int);
            assert(fst@ =~= slice@.subrange(0, rem as int));
            assert((fst@.len() as int) == rem as int);
            assert((fst@.len() as int) < c);
        }
        Self { v: snd, rem: fst, chunk_size }
    }

    pub const fn remainder(&self) -> (ret: &'a [T])
        ensures
            ret@ == slice_iterator_view(self).remainder,
            ret@.len() < slice_iterator_view(self).chunk_size,
    {
        proof {
            reveal(slice_iterator_view);
            use_type_invariant(self);
        }
        self.rem
    }
}

}
