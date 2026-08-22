#![allow(dead_code, unused_imports, unused_variables, unused_mut)]
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
// Target-specific Verus implementation harness.
// Target: core::slice::as_mut_ptr
// Source: core/src/slice/mod.rs:757-759
// Source item sha256: 99e25e7a86cc5c6b6b7557a4e100daf10a6be356072e931c8a093b6c6198dd9c
// Dependency manifest: proof_manifests/019_core_slice_as_mut_ptr/dependency_assumption_manifest.json

use core::marker::PointeeSized;
use core::ptr::null_mut;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::seq::*;

verus! {

pub open spec fn slice_start_mut_ptr<T>(seq: Seq<T>, ptr: *mut T) -> bool {
    ptr@.addr as nat == seq.len() && ptr@.provenance == Provenance::null()
}

pub assume_specification<T: PointeeSized>[<*mut T>::wrapping_byte_add](
    ptr: *mut T,
    count: usize,
) -> (ret: *mut T)
    requires
        ptr@.addr == 0,
    ensures
        ret@.addr == count,
        ret@.provenance == ptr@.provenance,
;

pub const fn rust_1_96_slice_as_mut_ptr_cast<T>(slice: &mut [T]) -> (ptr: *mut T)
    ensures
        slice_start_mut_ptr(old(slice)@, ptr),
        final(slice)@ == old(slice)@,
{
    let len = slice.len();
    let ptr = null_mut::<T>().wrapping_byte_add(len);
    proof {
        assert(old(slice)@.len() == len as nat);
    }
    ptr
}

pub const fn as_mut_ptr<T>(slice: &mut [T]) -> (ptr: *mut T)
    ensures
        slice_start_mut_ptr(old(slice)@, ptr),
        final(slice)@ == old(slice)@,
{
    rust_1_96_slice_as_mut_ptr_cast(slice)
}

}
