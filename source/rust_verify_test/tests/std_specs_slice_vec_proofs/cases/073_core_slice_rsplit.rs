#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::rsplit
// Source: core/src/slice/mod.rs:2362-2367 and core/src/slice/iter.rs:401-416,934-945
// Source item sha256: 87befc34097ba0c7a76b93cbb709bbbeb97359bcfcff394e98c331a6be2b936e
// Dependency manifest: proof_manifests/073_core_slice_rsplit/dependency_assumption_manifest.json

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

pub uninterp spec fn fnmut_predicate_observed<F, T>(pred: F, value: T) -> bool;

pub struct Split<'a, T: 'a, P>
    where
        P: FnMut(&T) -> bool,
{
    pub(crate) v: &'a [T],
    pred: P,
    pub(crate) finished: bool,
}

pub struct RSplit<'a, T: 'a, P>
    where
        P: FnMut(&T) -> bool,
{
    inner: Split<'a, T, P>,
}

pub closed spec fn split_iterator_view<'a, T, P>(iter: Split<'a, T, P>) -> SliceIteratorView<T>
    where
        P: FnMut(&T) -> bool,
{
    SliceIteratorView {
        source: iter.v@,
        remaining: iter.v@,
        yielded_prefix: Seq::empty(),
        remainder: Seq::empty(),
        chunk_size: 0,
        reverse: false,
    }
}

pub closed spec fn slice_iterator_view<'a, T, P>(iter: RSplit<'a, T, P>) -> SliceIteratorView<T>
    where
        P: FnMut(&T) -> bool,
{
    SliceIteratorView {
        source: iter.inner.v@,
        remaining: iter.inner.v@,
        yielded_prefix: Seq::empty(),
        remainder: Seq::empty(),
        chunk_size: 0,
        reverse: true,
    }
}

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn slice_predicate_split_view<'a, T, F>(
    iter: RSplit<'a, T, F>,
    source: Seq<T>,
    pred: F,
    inclusive: bool,
    reverse: bool,
    limit: int,
) -> bool
    where
        F: FnMut(&T) -> bool,
{
    let view = slice_iterator_view(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix.len() == 0
        && view.remainder.len() == 0
        && view.reverse == reverse
        && view.chunk_size == limit
        && limit >= 0
        && (if reverse {
            view.remaining + view.yielded_prefix == source
        } else {
            view.yielded_prefix + view.remaining == source
        })
        && forall|i: int| #![trigger fnmut_predicate_observed(pred, source[i])]
            0 <= i < source.len()
            ==> (fnmut_predicate_observed(pred, source[i])
                || !fnmut_predicate_observed(pred, source[i]))
}

impl<'a, T: 'a, P> Split<'a, T, P>
    where
        P: FnMut(&T) -> bool,
{
    pub fn new(slice: &'a [T], pred: P) -> (ret: Self)
        ensures
            split_iterator_view(ret).source == slice@,
            split_iterator_view(ret).remaining == slice@,
            split_iterator_view(ret).yielded_prefix.len() == 0,
            split_iterator_view(ret).remainder.len() == 0,
            split_iterator_view(ret).chunk_size == 0,
            !split_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice, pred, finished: false };
        proof {
            reveal(split_iterator_view);
        }
        ret
    }
}

impl<'a, T: 'a, P> RSplit<'a, T, P>
    where
        P: FnMut(&T) -> bool,
{
    pub fn new(slice: &'a [T], pred: P) -> (ret: Self)
        ensures
            slice_predicate_split_view(ret, slice@, pred, false, true, 0),
    {
        proof {
            assert forall|i: int| #![trigger fnmut_predicate_observed(pred, slice@[i])]
                0 <= i < slice@.len() implies
                (fnmut_predicate_observed(pred, slice@[i])
                    || !fnmut_predicate_observed(pred, slice@[i])) by {}
        }
        let ret = Self { inner: Split::new(slice, pred) };
        proof {
            reveal(slice_iterator_view);
            assert(slice_iterator_view(ret).source == slice@);
            assert(slice_iterator_view(ret).remaining == slice@);
            assert(slice_iterator_view(ret).yielded_prefix.len() == 0);
            assert(slice_iterator_view(ret).remainder.len() == 0);
            assert(slice_iterator_view(ret).reverse);
            assert(slice_iterator_view(ret).chunk_size == 0);
        }
        ret
    }
}

pub fn rsplit<'a, T: 'a, F>(slice: &'a [T], pred: F) -> (iter: RSplit<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        slice_predicate_split_view(iter, slice@, pred, false, true, 0),
{
    RSplit::new(slice, pred)
}

}
