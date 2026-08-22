#![allow(dead_code, unused_imports, unused_variables, unused_mut)]
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
// Target-specific Verus implementation harness.
// Target: core::slice::as_ptr
// Source: core/src/slice/mod.rs:726-728
// Source item sha256: df0d49a1417773cb8932d48e9e7bb06a553039beaca7f20000b9fc6319236c1d
// Dependency manifest: proof_manifests/021_core_slice_as_ptr/dependency_assumption_manifest.json

use core::marker::PointeeSized;
use core::ptr::null;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::seq::*;

verus! {

pub open spec fn slice_start_ptr<T>(seq: Seq<T>, ptr: *const T) -> bool {
    ptr@.addr as nat == seq.len() && ptr@.provenance == Provenance::null()
}

pub assume_specification<T: PointeeSized>[<*const T>::wrapping_byte_add](
    ptr: *const T,
    count: usize,
) -> (ret: *const T)
    requires
        ptr@.addr == 0,
    ensures
        ret@.addr == count,
        ret@.provenance == ptr@.provenance,
;

pub const fn rust_1_96_slice_as_ptr_cast<T>(slice: &[T]) -> (ptr: *const T)
    ensures
        slice_start_ptr(slice@, ptr),
{
    let len = slice.len();
    let ptr = null::<T>().wrapping_byte_add(len);
    proof {
        assert(slice@.len() == len as nat);
    }
    ptr
}

pub const fn as_ptr<T>(slice: &[T]) -> (ptr: *const T)
    ensures
        slice_start_ptr(slice@, ptr),
{
    rust_1_96_slice_as_ptr_cast(slice)
}

}
