#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::rsplitn
// Source: core/src/slice/mod.rs:2471-2476 and core/src/slice/iter.rs:401-416,934-945,1105-1108,1201-1212
// Source item sha256: 86062e6552f5f3f5acb7d888d78cb794de01f47658e9b5e83adee47a574766cd
// Dependency manifest: proof_manifests/075_core_slice_rsplitn/dependency_assumption_manifest.json

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

struct GenericSplitN<I> {
    iter: I,
    count: usize,
}

pub struct RSplitN<'a, T: 'a, P>
    where
        P: FnMut(&T) -> bool,
{
    inner: GenericSplitN<RSplit<'a, T, P>>,
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

pub closed spec fn rsplit_iterator_view<'a, T, P>(iter: RSplit<'a, T, P>) -> SliceIteratorView<T>
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

pub closed spec fn slice_iterator_view<'a, T, P>(iter: RSplitN<'a, T, P>) -> SliceIteratorView<T>
    where
        P: FnMut(&T) -> bool,
{
    let inner = rsplit_iterator_view(iter.inner.iter);
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

pub open spec fn rsplit_predicate_split_view<'a, T, F>(
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
    let view = rsplit_iterator_view(iter);
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
    iter: RSplitN<'a, T, F>,
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
            rsplit_predicate_split_view(ret, slice@, pred, false, true, 0),
    {
        proof {
            assert forall|i: int| #![trigger fnmut_predicate_observed(pred, slice@[i])]
                0 <= i < slice@.len() implies
                (fnmut_predicate_observed(pred, slice@[i])
                    || !fnmut_predicate_observed(pred, slice@[i])) by {}
        }
        let ret = Self { inner: Split::new(slice, pred) };
        proof {
            reveal(rsplit_iterator_view);
            assert(rsplit_iterator_view(ret).source == slice@);
            assert(rsplit_iterator_view(ret).remaining == slice@);
            assert(rsplit_iterator_view(ret).yielded_prefix.len() == 0);
            assert(rsplit_iterator_view(ret).remainder.len() == 0);
            assert(rsplit_iterator_view(ret).reverse);
            assert(rsplit_iterator_view(ret).chunk_size == 0);
        }
        ret
    }
}

impl<'a, T: 'a, P> RSplitN<'a, T, P>
    where
        P: FnMut(&T) -> bool,
{
    pub fn new(s: RSplit<'a, T, P>, n: usize) -> (ret: Self)
        ensures
            forall|source: Seq<T>, pred: P|
                rsplit_predicate_split_view(s, source, pred, false, true, 0)
                    ==> slice_predicate_split_view(ret, source, pred, false, true, n as int),
    {
        let ret = Self { inner: GenericSplitN { iter: s, count: n } };
        proof {
            reveal(slice_iterator_view);
            reveal(rsplit_iterator_view);
        }
        ret
    }
}

pub fn rsplit<'a, T: 'a, F>(slice: &'a [T], pred: F) -> (iter: RSplit<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        rsplit_predicate_split_view(iter, slice@, pred, false, true, 0),
{
    RSplit::new(slice, pred)
}

pub fn rsplitn<'a, T: 'a, F>(slice: &'a [T], n: usize, pred: F) -> (iter: RSplitN<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        slice_predicate_split_view(iter, slice@, pred, false, true, n as int),
{
    RSplitN::new(rsplit(slice, pred), n)
}

}
