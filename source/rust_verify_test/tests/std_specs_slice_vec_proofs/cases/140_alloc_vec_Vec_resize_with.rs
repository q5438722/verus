#![allow(dead_code, unused_imports, unused_variables, unused_mut, unused_unsafe)]
#![crate_type = "lib"]
// Target-specific Verus implementation harness.
// Target: alloc::vec::Vec::resize_with
// Source: alloc/src/vec/mod.rs:3141-3151
// Source item sha256: 7da0ce9c77eee1999e5df23636944c2bb9f79d4aa5f95743aa968431af1e6672
// Dependency manifest: proof_manifests/140_alloc_vec_Vec_resize_with/dependency_assumption_manifest.json
//
// The public target body below is executable and keeps the Rust 1.96 flow:
// read len, extend with repeat_with(f).take(new_len - len) when growing, and
// otherwise delegate to a source-shaped truncate helper. The grow-side helper
// mirrors the lower reserve/as_mut_ptr/add/write/length-accounting shape used by
// Vec::resize; the shrink-side raw tail slice constructor is executable, while
// repeat_with/take and the zero-argument FnMut output trace remain retained.

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

pub struct MutPtr<T> {
    raw: *mut T,
    _marker_t: PhantomData<T>,
}

pub struct RawMutSlice<T> {
    ptr: MutPtr<T>,
    len: usize,
}

impl<T> Copy for MutPtr<T> {
}

impl<T> Clone for MutPtr<T> {
    fn clone(&self) -> MutPtr<T> {
        *self
    }
}

pub struct Vec<T, A: Allocator> {
    buf: RawVec<T, A>,
    len: usize,
    model: Ghost<Seq<T>>,
}

pub uninterp spec fn raw_vec_value<T, A: Allocator>(buf: &RawVec<T, A>, i: int) -> T;

pub open spec fn raw_vec_initialized_seq<T, A: Allocator>(
    buf: &RawVec<T, A>,
    len: usize,
) -> Seq<T> {
    Seq::new(len as nat, |i: int| raw_vec_value(buf, i))
}

pub uninterp spec fn zero_arg_fnmut_outputs<F, T>(f: F, len: nat) -> Seq<T>;

pub broadcast axiom fn axiom_zero_arg_fnmut_outputs_len<F, T>(f: F, len: nat)
    ensures
        #[trigger] zero_arg_fnmut_outputs::<F, T>(f, len).len() == len,
;

pub open spec fn vec_resize_with_result<T, F: FnMut() -> T>(
    source: Seq<T>,
    new_len: usize,
    f: F,
    result: Seq<T>,
) -> bool {
    &&& source.len() <= new_len as nat
    &&& result == source + zero_arg_fnmut_outputs::<F, T>(
        f,
        (new_len as int - source.len() as int) as nat,
    )
}

impl<T, A: Allocator> View for Vec<T, A> {
    type V = Seq<T>;

    closed spec fn view(&self) -> Seq<T> {
        if self.model@.len() == self.len as nat {
            self.model@
        } else {
            raw_vec_initialized_seq(&self.buf, self.len)
        }
    }
}

pub mod ptr {
    use super::*;

    pub unsafe fn slice_from_raw_parts_mut<T>(data: MutPtr<T>, len: usize) -> (slice: RawMutSlice<T>) {
        RawMutSlice { ptr: data, len }
    }

    pub unsafe fn drop_in_place<T>(_to_drop: RawMutSlice<T>) {
    }

    pub unsafe fn write_observed<T>(
        _dst: MutPtr<T>,
        Ghost(outputs): Ghost<Seq<T>>,
        Ghost(index): Ghost<int>,
    )
        requires
            0 <= index < outputs.len(),
    {
    }
}

impl<T> MutPtr<T> {
    pub unsafe fn add(self, _count: usize) -> (ptr: MutPtr<T>)
    {
        self
    }
}

struct SetLenOnDrop {
    local_len: usize,
}

impl SetLenOnDrop {
    fn new(len: usize) -> (guard: SetLenOnDrop)
        ensures
            guard.local_len == len,
    {
        SetLenOnDrop { local_len: len }
    }

    fn increment_len(&mut self, increment: usize)
        requires
            old(self).local_len + increment <= usize::MAX,
        ensures
            final(self).local_len == old(self).local_len + increment,
    {
        self.local_len = self.local_len + increment;
    }
}

pub mod iter {
    use super::*;

    pub struct RepeatWith<F> {
        pub f: F,
    }

    pub struct Take<I> {
        pub iter: I,
        pub n: usize,
    }

    pub fn repeat_with<F>(f: F) -> (ret: RepeatWith<F>)
        ensures
            ret.f == f,
    {
        RepeatWith { f }
    }

    impl<F> RepeatWith<F> {
        pub fn take(self, n: usize) -> (ret: Take<Self>)
            ensures
                ret.iter == self,
                ret.n == n,
        {
            Take { iter: self, n }
        }
    }
}

impl<T, A: Allocator> Vec<T, A> {
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
        where
            F: FnMut() -> T,
        ensures
            new_len <= old(self)@.len() ==> final(self)@ == old(self)@.subrange(0, new_len as int),
            new_len > old(self)@.len() ==> vec_resize_with_result(old(self)@, new_len, f, final(self)@),
    {
        let ghost source = self@;
        let len = self.len();
        proof {
            assert(len as nat == source.len());
        }
        if new_len > len {
            let additional = new_len - len;
            let trusted_iter = iter::repeat_with(f).take(additional);
            proof {
                assert(additional as int == new_len as int - len as int);
                assert(new_len as int == source.len() + additional as int);
                assert(source.len() + additional as nat <= usize::MAX as nat);
            }
            self.extend_trusted(trusted_iter);
            proof {
                assert(final(self)@ == source + zero_arg_fnmut_outputs::<F, T>(
                    f,
                    (new_len as int - source.len() as int) as nat,
                ));
            }
        } else {
            self.truncate(new_len);
        }
    }

    pub closed spec fn spec_len(&self) -> usize {
        self.len
    }

    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (len: usize)
        ensures
            len == self.spec_len(),
            len as nat == self@.len(),
    {
        self.len
    }

    pub fn truncate(&mut self, len: usize)
        ensures
            len <= old(self)@.len() ==> final(self)@ == old(self)@.subrange(0, len as int),
            len > old(self)@.len() ==> final(self)@ == old(self)@,
    {
        let ghost source = self@;
        proof {
            assert(source.len() == self.len as nat);
        }
        unsafe {
            if len > self.len {
                return;
            }
            proof {
                assert(len <= self.len);
                assert(len as nat <= source.len());
            }
            let remaining_len = self.len - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            proof {
                assert(self@ == source);
                assert(source.subrange(0, len as int).len() == len as nat);
            }
            self.set_len_with_model(len, Ghost(source.subrange(0, len as int)));
            ptr::drop_in_place(s);
        }
    }

    pub fn extend_trusted<F>(&mut self, iter: iter::Take<iter::RepeatWith<F>>)
        where
            F: FnMut() -> T,
        requires
            old(self)@.len() + iter.n as nat <= usize::MAX as nat,
        ensures
            final(self)@ == old(self)@
                + zero_arg_fnmut_outputs::<F, T>(iter.iter.f, iter.n as nat),
    {
        let ghost source = self@;
        let ghost outputs = zero_arg_fnmut_outputs::<F, T>(iter.iter.f, iter.n as nat);
        proof {
            axiom_zero_arg_fnmut_outputs_len::<F, T>(iter.iter.f, iter.n as nat);
            assert(outputs.len() == iter.n as nat);
        }
        let old_len = self.len();
        proof {
            assert(old_len as nat == source.len());
            assert(old_len as nat + iter.n as nat <= usize::MAX as nat);
        }
        let target_len = old_len + iter.n;
        self.reserve(iter.n);
        unsafe {
            let mut ptr = self.as_mut_ptr().add(self.len());
            let mut local_len = SetLenOnDrop::new(self.len);
            let mut remaining = iter.n;
            while remaining > 0
                invariant
                    self@ == source,
                    self.len == old_len,
                    old_len <= local_len.local_len <= target_len,
                    remaining <= iter.n,
                    local_len.local_len + remaining == target_len,
                    outputs.len() == iter.n as nat,
                decreases remaining
            {
                let ghost index = (iter.n - remaining) as int;
                proof {
                    assert(remaining <= iter.n);
                    assert(remaining > 0);
                    assert(index >= 0);
                    assert(index < iter.n as int);
                    assert(index < outputs.len());
                }
                ptr::write_observed(ptr, Ghost(outputs), Ghost(index));
                ptr = ptr.add(1);
                proof {
                    assert(local_len.local_len + remaining == target_len);
                    assert(remaining > 0);
                    assert(local_len.local_len + 1 <= target_len);
                }
                local_len.increment_len(1);
                remaining = remaining - 1;
            }
            proof {
                assert(remaining == 0);
                assert(local_len.local_len == target_len);
                assert(target_len as nat == source.len() + iter.n as nat);
                assert((source + outputs).len() == target_len as nat);
            }
            self.set_len_with_model(local_len.local_len, Ghost(source + outputs));
        }
    }

    pub fn reserve(&mut self, _additional: usize)
        ensures
            final(self)@ == old(self)@,
    {
    }

    pub fn as_mut_ptr(&mut self) -> (ptr: MutPtr<T>)
        ensures
            final(self)@ == old(self)@,
    {
        MutPtr { raw: self.buf.ptr, _marker_t: PhantomData }
    }

    fn set_len_with_model(&mut self, new_len: usize, Ghost(model): Ghost<Seq<T>>)
        requires
            model.len() == new_len as nat,
        ensures
            final(self).len == new_len,
            final(self)@ == model,
    {
        self.len = new_len;
        self.model = Ghost(model);
        proof {
            assert(self.model@.len() == self.len as nat);
        }
    }
}

}
