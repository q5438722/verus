#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::rchunks_exact
// Source: core/src/slice/mod.rs:1775-1778 and core/src/slice/iter.rs:2653-2666
// Source item sha256: 6b74e9fdc203699eb8b38833da4d97d1d4077128f349673a72ef680166449878
// Dependency manifest: proof_manifests/067_core_slice_rchunks_exact/dependency_assumption_manifest.json

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

pub struct RChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: RChunksExact<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.rem@ + iter.v@,
        remaining: iter.v@,
        yielded_prefix: Seq::empty(),
        remainder: iter.rem@,
        chunk_size: iter.chunk_size as int,
        reverse: true,
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

impl<'a, T> RChunksExact<'a, T> {
    pub const fn new(slice: &'a [T], chunk_size: usize) -> (ret: Self)
        requires
            chunk_size != 0,
        ensures
            slice_iterator_view(ret).source == slice@,
            slice_iterator_view(ret).yielded_prefix == Seq::empty(),
            slice_iterator_view(ret).chunk_size == chunk_size as int,
            slice_iterator_view(ret).reverse,
            slice_chunk_partition(slice_iterator_view(ret)),
    {
        let rem = slice.len() % chunk_size;
        proof {
            lemma_mod_decreases(slice.len() as nat, chunk_size as nat);
            assert(rem <= slice.len());
        }
        let (fst, snd) = slice.split_at(rem);
        let ret = Self { v: snd, rem: fst, chunk_size };
        proof {
            let n = slice.len() as int;
            let c = chunk_size as int;
            lemma_mod_division_less_than_divisor(n, c);
            lemma_fundamental_div_mod(n, c);
            lemma_mod_multiples_basic(n / c, c);
            lemma_mul_is_commutative(c, n / c);
            assert(0 <= rem as int);
            assert((rem as int) < c);
            assert(n == c * (n / c) + (n % c));
            assert(n - (rem as int) == c * (n / c));
            assert(c * (n / c) == (n / c) * c);
            assert((n - (rem as int)) % c == 0);
            reveal(slice_iterator_view);
            slice@.lemma_split_at(rem as int);
            assert(fst@ =~= slice@.subrange(0, rem as int));
            assert(snd@ =~= slice@.subrange(rem as int, slice@.len() as int));
            assert(fst@ + snd@ == slice@);
            assert((fst@.len() as int) == rem as int);
            assert((snd@.len() as int) == n - (rem as int));
            assert(slice_iterator_well_formed(slice_iterator_view(ret)));
            assert(slice_iterator_view(ret).chunk_size > 0);
            assert((slice_iterator_view(ret).remainder.len() as int) < slice_iterator_view(ret).chunk_size);
            assert((slice_iterator_view(ret).remaining.len() as int) % slice_iterator_view(ret).chunk_size == 0);
            lemma_small_mod(0nat, chunk_size as nat);
            assert(slice_iterator_view(ret).yielded_prefix == Seq::empty());
            assert(0int % slice_iterator_view(ret).chunk_size == 0);
            assert((slice_iterator_view(ret).yielded_prefix.len() as int) % slice_iterator_view(ret).chunk_size == 0);
            assert(slice_iterator_view(ret).reverse);
            assert(
                slice_iterator_view(ret).remainder + slice_iterator_view(ret).remaining
                    + slice_iterator_view(ret).yielded_prefix == slice_iterator_view(ret).source
            );
            assert(slice_chunk_partition(slice_iterator_view(ret)));
        }
        ret
    }
}

pub const fn rchunks_exact<'a, T>(slice: &'a [T], chunk_size: usize) -> (iter: RChunksExact<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view(iter).chunk_size == chunk_size as int,
        slice_iterator_view(iter).reverse,
        slice_chunk_partition(slice_iterator_view(iter)),
{
    assert(chunk_size != 0);
    RChunksExact::new(slice, chunk_size)
}

}
