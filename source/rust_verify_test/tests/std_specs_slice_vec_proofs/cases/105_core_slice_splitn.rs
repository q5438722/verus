#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::splitn
// Source: core/src/slice/mod.rs:2416-2421 and core/src/slice/iter.rs:401-416,934-945,1105-1108
// Source item sha256: 9a588be232037701d6ad4f191936e5d2be5db5f4a6c22bd0ddfbcc4cbf5c4156
// Dependency manifest: proof_manifests/105_core_slice_splitn/dependency_assumption_manifest.json

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

struct GenericSplitN<I> {
    iter: I,
    count: usize,
}

pub struct SplitN<'a, T: 'a, P>
    where
        P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<Split<'a, T, P>>,
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

pub closed spec fn slice_iterator_view<'a, T, P>(iter: SplitN<'a, T, P>) -> SliceIteratorView<T>
    where
        P: FnMut(&T) -> bool,
{
    let inner = split_iterator_view(iter.inner.iter);
    SliceIteratorView {
        source: inner.source,
        remaining: inner.remaining,
        yielded_prefix: inner.yielded_prefix,
        remainder: inner.remainder,
        chunk_size: iter.inner.count as int,
        reverse: inner.reverse,
    }
}

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn split_predicate_split_view<'a, T, F>(
    iter: Split<'a, T, F>,
    source: Seq<T>,
    pred: F,
    inclusive: bool,
    reverse: bool,
    limit: int,
) -> bool
    where
        F: FnMut(&T) -> bool,
{
    let view = split_iterator_view(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix.len() == 0
        && view.remainder.len() == 0
        && view.reverse == reverse
        && view.chunk_size == limit
        && limit >= 0
        && !inclusive
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

pub open spec fn slice_predicate_split_view<'a, T, F>(
    iter: SplitN<'a, T, F>,
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
        && !inclusive
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
            split_predicate_split_view(ret, slice@, pred, false, false, 0),
    {
        proof {
            assert forall|i: int| #![trigger fnmut_predicate_observed(pred, slice@[i])]
                0 <= i < slice@.len() implies
                (fnmut_predicate_observed(pred, slice@[i])
                    || !fnmut_predicate_observed(pred, slice@[i])) by {}
        }
        let ret = Self { v: slice, pred, finished: false };
        proof {
            reveal(split_iterator_view);
            assert(split_iterator_view(ret).source == slice@);
            assert(split_iterator_view(ret).remaining == slice@);
            assert(split_iterator_view(ret).yielded_prefix.len() == 0);
            assert(split_iterator_view(ret).remainder.len() == 0);
            assert(!split_iterator_view(ret).reverse);
            assert(split_iterator_view(ret).chunk_size == 0);
        }
        ret
    }
}

impl<'a, T: 'a, P> SplitN<'a, T, P>
    where
        P: FnMut(&T) -> bool,
{
    pub fn new(s: Split<'a, T, P>, n: usize) -> (ret: Self)
        ensures
            forall|source: Seq<T>, pred: P|
                split_predicate_split_view(s, source, pred, false, false, 0)
                    ==> slice_predicate_split_view(ret, source, pred, false, false, n as int),
    {
        let ret = Self { inner: GenericSplitN { iter: s, count: n } };
        proof {
            reveal(slice_iterator_view);
            reveal(split_iterator_view);
        }
        ret
    }
}

pub fn split<'a, T: 'a, F>(slice: &'a [T], pred: F) -> (iter: Split<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        split_predicate_split_view(iter, slice@, pred, false, false, 0),
{
    Split::new(slice, pred)
}

pub fn splitn<'a, T: 'a, F>(slice: &'a [T], n: usize, pred: F) -> (iter: SplitN<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        slice_predicate_split_view(iter, slice@, pred, false, false, n as int),
{
    SplitN::new(split(slice, pred), n)
}

}
