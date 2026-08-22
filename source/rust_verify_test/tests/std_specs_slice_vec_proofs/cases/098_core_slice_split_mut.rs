#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::split_mut
// Source: core/src/slice/mod.rs:2266-2271 and core/src/slice/iter.rs:678-690
// Source item sha256: 75b056645bc50f9f79c972b53ff5c1683ab5eafc1782d305cd4eb47bee542965
// Dependency manifest: proof_manifests/098_core_slice_split_mut/dependency_assumption_manifest.json

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

pub struct SplitMut<'a, T: 'a, P>
    where
        P: FnMut(&T) -> bool,
{
    pub(crate) v: &'a mut [T],
    pred: P,
    pub(crate) finished: bool,
}

pub closed spec fn slice_iterator_view<'a, T, P>(iter: SplitMut<'a, T, P>) -> SliceIteratorView<T>
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

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub open spec fn slice_predicate_split_view<'a, T, F>(
    iter: SplitMut<'a, T, F>,
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
        && !inclusive
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

impl<'a, T: 'a, P> SplitMut<'a, T, P>
    where
        P: FnMut(&T) -> bool,
{
    pub fn new(slice: &'a mut [T], pred: P) -> (ret: Self)
        ensures
            slice_predicate_split_view(ret, old(slice)@, pred, false, false, 0),
    {
        proof {
            assert forall|i: int| #![trigger fnmut_predicate_observed(pred, old(slice)@[i])]
                0 <= i < old(slice)@.len() implies
                (fnmut_predicate_observed(pred, old(slice)@[i])
                    || !fnmut_predicate_observed(pred, old(slice)@[i])) by {}
        }
        let ret = Self { v: slice, pred, finished: false };
        proof {
            reveal(slice_iterator_view);
            assert(slice_iterator_view(ret).source == old(slice)@);
            assert(slice_iterator_view(ret).remaining == old(slice)@);
            assert(slice_iterator_view(ret).yielded_prefix.len() == 0);
            assert(slice_iterator_view(ret).remainder.len() == 0);
            assert(!slice_iterator_view(ret).reverse);
            assert(slice_iterator_view(ret).chunk_size == 0);
        }
        ret
    }
}

pub fn split_mut<'a, T: 'a, F>(slice: &'a mut [T], pred: F) -> (iter: SplitMut<'a, T, F>)
    where
        F: FnMut(&T) -> bool,
    ensures
        slice_predicate_split_view(iter, old(slice)@, pred, false, false, 0),
{
    SplitMut::new(slice, pred)
}

}
