#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::chunks_exact_mut
// Source: core/src/slice/mod.rs:1290-1293 and core/src/slice/iter.rs:2013-2033
// Source item sha256: 8af861fb41a485b218b14d2d109bfa84e040bef3dd2a6bdf393196536a734456
// Dependency manifest: proof_manifests/035_core_slice_chunks_exact_mut/dependency_assumption_manifest.json

use core::marker::PhantomData;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::seq_lib::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub remaining: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct ChunksExactMut<'a, T: 'a> {
    v: &'a mut [T],
    rem: &'a mut [T],
    chunk_size: usize,
    _marker: PhantomData<&'a mut T>,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: ChunksExactMut<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@ + iter.rem@,
        remaining: iter.v@,
        yielded_prefix: Seq::empty(),
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: false,
    }
}

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn slice_chunk_partition<T>(view: SliceIteratorView<T>) -> bool {
    slice_iterator_well_formed(view)
        && view.chunk_size > 0
        && (view.remainder.len() as int) < view.chunk_size
        && (view.remaining.len() as int) % view.chunk_size == 0
        && (view.yielded_prefix.len() as int) % view.chunk_size == 0
        && if view.reverse {
            view.remainder + view.remaining + view.yielded_prefix == view.source
        } else {
            view.yielded_prefix + view.remaining + view.remainder == view.source
        }
}

impl<'a, T> ChunksExactMut<'a, T> {
    pub const fn new(slice: &'a mut [T], chunk_size: usize) -> (ret: Self)
        requires
            chunk_size != 0,
        ensures
            slice_iterator_view(ret).source == old(slice)@,
            slice_iterator_view(ret).yielded_prefix == Seq::empty(),
            slice_iterator_view(ret).chunk_size == chunk_size as int,
            !slice_iterator_view(ret).reverse,
            slice_chunk_partition(slice_iterator_view(ret)),
    {
        let ghost source = slice@;
        let rem = slice.len() % chunk_size;
        proof {
            lemma_mod_decreases(slice.len() as nat, chunk_size as nat);
            assert(rem <= slice.len());
        }
        let fst_len = slice.len() - rem;
        let (fst, snd) = slice.split_at_mut(fst_len);
        let ret = Self { v: fst, rem: snd, chunk_size, _marker: PhantomData };
        proof {
            let n = source.len() as int;
            let c = chunk_size as int;
            lemma_mod_division_less_than_divisor(n, c);
            lemma_fundamental_div_mod(n, c);
            lemma_mod_multiples_basic(n / c, c);
            lemma_mul_is_commutative(c, n / c);
            assert(0 <= rem as int);
            assert((rem as int) < c);
            assert((fst_len as int) == n - (rem as int));
            assert(n == c * (n / c) + (n % c));
            assert((fst_len as int) == c * (n / c));
            assert(c * (n / c) == (n / c) * c);
            assert((fst_len as int) % c == 0);
            reveal(slice_iterator_view);
            source.lemma_split_at(fst_len as int);
            assert(ret.v@ =~= source.subrange(0, fst_len as int));
            assert(ret.rem@ =~= source.subrange(fst_len as int, source.len() as int));
            assert(ret.v@ + ret.rem@ == source);
            assert((ret.rem@.len() as int) == rem as int);
            assert((ret.v@.len() as int) == fst_len as int);
            assert(slice_iterator_well_formed(slice_iterator_view(ret)));
            assert(slice_iterator_view(ret).chunk_size > 0);
            assert((slice_iterator_view(ret).remainder.len() as int) < slice_iterator_view(ret).chunk_size);
            assert((slice_iterator_view(ret).remaining.len() as int) % slice_iterator_view(ret).chunk_size == 0);
            lemma_small_mod(0nat, chunk_size as nat);
            assert(slice_iterator_view(ret).yielded_prefix == Seq::empty());
            assert(0int % slice_iterator_view(ret).chunk_size == 0);
            assert((slice_iterator_view(ret).yielded_prefix.len() as int) % slice_iterator_view(ret).chunk_size == 0);
            assert(!slice_iterator_view(ret).reverse);
            assert(
                slice_iterator_view(ret).yielded_prefix + slice_iterator_view(ret).remaining
                    + slice_iterator_view(ret).remainder == slice_iterator_view(ret).source
            );
            assert(slice_chunk_partition(slice_iterator_view(ret)));
        }
        ret
    }
}

pub const fn chunks_exact_mut<'a, T>(slice: &'a mut [T], chunk_size: usize) -> (iter: ChunksExactMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view(iter).source == old(slice)@,
        slice_iterator_view(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view(iter).chunk_size == chunk_size as int,
        !slice_iterator_view(iter).reverse,
        slice_chunk_partition(slice_iterator_view(iter)),
{
    assert(chunk_size != 0);
    ChunksExactMut::new(slice, chunk_size)
}

}
