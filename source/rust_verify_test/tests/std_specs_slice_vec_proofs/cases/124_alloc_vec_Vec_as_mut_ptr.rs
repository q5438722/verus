#![allow(dead_code, unused_imports, unused_variables, unused_mut)]
// Target-specific Verus implementation harness.
// Target: alloc::vec::Vec::as_mut_ptr
// Source: alloc/src/vec/mod.rs:2022-2026 and alloc/raw_vec/mod.rs:73-75, 295-297, 608-610
// Source item sha256: 56c46d9ef725e15cd271f3f23002feff485277b74e9e73f1bf9b87663be0718b
// Dependency manifest: proof_manifests/124_alloc_vec_Vec_as_mut_ptr/dependency_assumption_manifest.json

use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::view::*;

verus! {

pub trait Allocator {
}

pub struct RawVec<T, A: Allocator> {
    ptr: *mut T,
    _marker_t: PhantomData<T>,
    _marker_a: PhantomData<A>,
}

pub struct Vec<T, A: Allocator> {
    buf: RawVec<T, A>,
    len: usize,
}

pub trait CapacitySpec {
    spec fn spec_capacity(&self) -> nat;
}

pub uninterp spec fn raw_mut_ptr_value<T>(ptr: *mut T, i: int) -> T;

pub uninterp spec fn raw_mut_ptr_capacity<T>(ptr: *mut T) -> nat;

pub open spec fn raw_mut_ptr_initialized_seq<T>(ptr: *mut T, len: nat) -> Seq<T> {
    Seq::new(len, |i: int| raw_mut_ptr_value(ptr, i))
}

closed spec fn raw_vec_initialized_seq<T, A: Allocator>(
    buf: &RawVec<T, A>,
    len: usize,
) -> Seq<T> {
    raw_mut_ptr_initialized_seq(buf.ptr, len as nat)
}

closed spec fn raw_vec_capacity<T, A: Allocator>(buf: &RawVec<T, A>) -> nat {
    raw_mut_ptr_capacity(buf.ptr)
}

pub open spec fn vec_start_mut_ptr<T>(seq: Seq<T>, capacity: nat, ptr: *mut T) -> bool {
    seq == raw_mut_ptr_initialized_seq(ptr, seq.len()) && capacity == raw_mut_ptr_capacity(ptr)
}

impl<T, A: Allocator> View for Vec<T, A> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Seq<T> {
        raw_vec_initialized_seq(&self.buf, self.len)
    }
}

impl<T, A: Allocator> CapacitySpec for Vec<T, A> {
    closed spec fn spec_capacity(&self) -> nat {
        raw_vec_capacity(&self.buf)
    }
}

impl<T, A: Allocator> Vec<T, A> {
    pub const fn as_mut_ptr(&mut self) -> (ptr: *mut T)
        ensures
            vec_start_mut_ptr(old(self)@, old(self).spec_capacity(), ptr),
            final(self)@ == old(self)@,
    {
        // We shadow the slice method of the same name to avoid going through
        // `deref_mut`, which creates an intermediate reference.
        let ghost source = self@;
        let ghost capacity = self.spec_capacity();
        let ptr = self.buf.ptr;
        proof {
            reveal(raw_vec_initialized_seq);
            reveal(raw_vec_capacity);
            assert(source == raw_mut_ptr_initialized_seq::<T>(ptr, self.len as nat));
            assert(source.len() == self.len as nat);
            assert(source == raw_mut_ptr_initialized_seq::<T>(ptr, source.len()));
            assert(capacity == raw_mut_ptr_capacity::<T>(ptr));
        }
        ptr
    }
}

}
