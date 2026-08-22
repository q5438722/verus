#![allow(dead_code, unused_imports, unused_variables)]
#![cfg_attr(verus_keep_ghost, feature(const_trait_impl))]
// Target-specific Verus implementation harness.
// Target: core::slice::get_mut
// Source: core/src/slice/mod.rs:599-604
// Source item sha256: 003625b19b151e26497787859485cf0ed9d8f38382d73e69831cd5de64758914
// Dependency manifest: proof_manifests/053_core_slice_get_mut/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub uninterp spec fn slice_index_in_range<T, I>(seq: Seq<T>, index: I) -> bool;

pub uninterp spec fn slice_index_mut_frame<T, I>(
    old_seq: Seq<T>,
    index: I,
    final_seq: Seq<T>,
) -> bool;

pub const trait SliceIndex<T> {
    type Output;

    fn get_mut<'a>(self, slice: &'a mut [T]) -> (ret: Option<&'a mut Self::Output>)
        ensures
            ret.is_some() ==> slice_index_in_range::<T, Self>(old(slice)@, self)
                && slice_index_mut_frame::<T, Self>(old(slice)@, self, final(slice)@),
            ret.is_none() ==> !slice_index_in_range::<T, Self>(old(slice)@, self)
                && final(slice)@ == old(slice)@;
}

pub const fn get_mut<'a, T, I>(
    slice: &'a mut [T],
    index: I,
) -> (ret: Option<&'a mut <I as SliceIndex<T>>::Output>)
    where
        I: [const] SliceIndex<T>,
    ensures
        ret.is_some() ==> slice_index_in_range::<T, I>(old(slice)@, index)
            && slice_index_mut_frame::<T, I>(old(slice)@, index, final(slice)@),
        ret.is_none() ==> !slice_index_in_range::<T, I>(old(slice)@, index)
            && final(slice)@ == old(slice)@,
{
    index.get_mut(slice)
}

}
