#![allow(dead_code, unused_imports, unused_variables, unused_mut, unused_unsafe)]
// Target-specific Verus implementation harness.
// Target: alloc::vec::Vec::set_len
// Source: alloc/src/vec/mod.rs:2187-2195
// Source item sha256: d38f2af683a66c0b8b52346907d857f4f6aebe7f28155d46ee9e615c230b98cb
// Dependency manifest: proof_manifests/143_alloc_vec_Vec_set_len/dependency_assumption_manifest.json
//
// The public target body below is executable and keeps the Rust 1.96 flow:
// check the unsafe precondition `new_len <= self.capacity()`, then assign
// `self.len = new_len`. Trusted boundaries are limited to the source-backed
// RawVec capacity/raw-storage view and the unsafe-precondition check.

use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::view::*;

verus! {

pub trait Allocator {
}

pub struct RawVec<T, A: Allocator> {
    cap: usize,
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

pub uninterp spec fn raw_vec_value<T, A: Allocator>(buf: &RawVec<T, A>, i: int) -> T;

pub closed spec fn raw_vec_capacity<T, A: Allocator>(buf: &RawVec<T, A>) -> nat {
    buf.cap as nat
}

pub open spec fn raw_vec_initialized_seq<T, A: Allocator>(
    buf: &RawVec<T, A>,
    len: usize,
) -> Seq<T> {
    Seq::new(len as nat, |i: int| raw_vec_value(buf, i))
}

pub open spec fn vec_set_len_domain<T>(seq: Seq<T>, capacity: nat, new_len: usize) -> bool {
    new_len as nat <= capacity
}

pub open spec fn vec_set_len_result<T>(
    old_seq: Seq<T>,
    capacity: nat,
    new_len: usize,
    final_seq: Seq<T>,
) -> bool {
    vec_set_len_domain(old_seq, capacity, new_len) && final_seq.len() == new_len as nat
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

pub mod ub_checks {
    use super::*;

    pub const fn assert_unsafe_precondition(new_len: usize, capacity: usize)
        requires
            new_len <= capacity,
    {
    }
}

impl<T, A: Allocator> RawVec<T, A> {
    pub const fn capacity(&self) -> (cap: usize)
        ensures
            cap as nat == raw_vec_capacity(self),
    {
        self.cap
    }
}

impl<T, A: Allocator> Vec<T, A> {
    pub const fn capacity(&self) -> (cap: usize)
        ensures
            cap as nat == self.spec_capacity(),
    {
        self.buf.capacity()
    }

    pub const unsafe fn set_len(&mut self, new_len: usize)
        requires
            vec_set_len_domain(old(self)@, old(self).spec_capacity(), new_len),
        ensures
            final(self)@.len() == new_len as nat,
            vec_set_len_result(old(self)@, old(self).spec_capacity(), new_len, final(self)@),
    {
        let capacity = self.capacity();
        proof {
            assert(vec_set_len_domain(old(self)@, old(self).spec_capacity(), new_len));
            assert(capacity as nat == old(self).spec_capacity());
            assert(new_len as nat <= capacity as nat);
            assert(new_len <= capacity);
        }
        ub_checks::assert_unsafe_precondition(new_len, capacity);

        self.len = new_len;
    }
}

}
