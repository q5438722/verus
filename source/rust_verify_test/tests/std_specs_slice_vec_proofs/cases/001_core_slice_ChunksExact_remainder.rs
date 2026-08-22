#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::ChunksExact::remainder
// Source: core/src/slice/iter.rs:1843-1880
// Source item sha256: 52c87daecc8119b00040a9a13d3d339571ba252c96f64bb463cfe834699e7bd0
// Dependency manifest: proof_manifests/001_core_slice_ChunksExact_remainder/dependency_assumption_manifest.json

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

pub struct ChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: &ChunksExact<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@ + iter.rem@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: false,
    }
}

impl<'a, T> ChunksExact<'a, T> {
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
        let fst_len = slice.len() - rem;
        let (fst, snd) = slice.split_at(fst_len);
        proof {
            let n = slice.len() as int;
            let c = chunk_size as int;
            lemma_mod_division_less_than_divisor(n, c);
            assert((rem as int) < c);
            assert((fst_len as int) == n - (rem as int));
            slice@.lemma_split_at(fst_len as int);
            assert(snd@ =~= slice@.subrange(fst_len as int, slice@.len() as int));
            assert((snd@.len() as int) == rem as int);
            assert((snd@.len() as int) < c);
        }
        Self { v: fst, rem: snd, chunk_size }
    }

    pub fn remainder(&self) -> (ret: &'a [T])
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
