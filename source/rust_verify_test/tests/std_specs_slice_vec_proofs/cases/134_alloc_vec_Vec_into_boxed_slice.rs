#![allow(dead_code, unused_imports, unused_variables, unused_mut, unused_unsafe)]
// Target-specific Verus implementation harness.
// Target: alloc::vec::Vec::into_boxed_slice
// Source: alloc/src/vec/mod.rs:1733-1741
// Source item sha256: 9e01645b7eb77565f8c9119a9d5c258092a94b937fe775ec0227e0be20e18f44
// Dependency manifest: proof_manifests/134_alloc_vec_Vec_into_boxed_slice/dependency_assumption_manifest.json
//
// The public target body below is executable and keeps the Rust 1.96 control/data
// flow. Vec::shrink_to_fit is executable here using the reviewed lower-level
// shape from its own harness: the Vec len/capacity fact is carried by a
// target-local type invariant, while the remaining shrink trust is RawVec allocator shrink. The other trusted
// RawVec::into_box (alloc/src/raw_vec/mod.rs:238-249) and
// Box<[MaybeUninit<T>]>::assume_init (alloc/src/boxed.rs:1229-1259) now execute
// as ghost-state conversions over the initialized-prefix model. The local
// ptr::read wrapper executes as the modeled RawVec field move.

use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::seq::*;
use vstd::view::*;

verus! {

pub trait Allocator {
}

pub struct RawVec<T, A: Allocator> {
    cap: usize,
    model: Ghost<Seq<T>>,
    _marker_t: PhantomData<T>,
    _marker_a: PhantomData<A>,
}

pub struct Vec<T, A: Allocator> {
    buf: RawVec<T, A>,
    len: usize,
}

pub struct ManuallyDrop<T, A: Allocator> {
    buf: RawVec<T, A>,
    len: usize,
}

pub struct BoxedMaybeUninitSlice<T, A: Allocator> {
    pub view: Ghost<Seq<T>>,
    pub capacity: Ghost<nat>,
    pub _marker_t: PhantomData<T>,
    pub _marker_a: PhantomData<A>,
}

pub struct BoxedSlice<T, A: Allocator> {
    pub view: Ghost<Seq<T>>,
    pub capacity: Ghost<nat>,
    pub _marker_t: PhantomData<T>,
    pub _marker_a: PhantomData<A>,
}

pub trait CapacitySpec {
    spec fn spec_capacity(&self) -> nat;
}

pub uninterp spec fn raw_vec_value<T, A: Allocator>(buf: &RawVec<T, A>, i: int) -> T;

pub closed spec fn raw_vec_initialized_seq<T, A: Allocator>(
    buf: &RawVec<T, A>,
    len: usize,
) -> Seq<T> {
    Seq::new(len as nat, |i: int|
        if 0 <= i < buf.model@.len() {
            buf.model@[i]
        } else {
            raw_vec_value(buf, i)
        })
}

pub closed spec fn raw_vec_capacity<T, A: Allocator>(buf: &RawVec<T, A>) -> nat {
    buf.cap as nat
}

pub open spec fn maybe_uninit_box_view<T, A: Allocator>(boxed: &BoxedMaybeUninitSlice<T, A>) -> Seq<T> {
    boxed.view@
}

pub open spec fn maybe_uninit_box_capacity<T, A: Allocator>(boxed: &BoxedMaybeUninitSlice<T, A>) -> nat {
    boxed.capacity@
}

pub open spec fn boxed_slice_view<T, A: Allocator>(boxed: BoxedSlice<T, A>) -> Seq<T> {
    boxed.view@
}

pub open spec fn boxed_slice_capacity<T, A: Allocator>(boxed: BoxedSlice<T, A>) -> nat {
    boxed.capacity@
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

impl<T, A: Allocator> RawVec<T, A> {
    pub fn capacity(&self) -> (cap: usize)
        ensures
            cap as nat == raw_vec_capacity(self),
    {
        self.cap
    }

    fn shrink_to_fit(&mut self, cap: usize)
        requires
            cap as nat <= raw_vec_capacity(old(self)),
            cap as nat <= old(self).model@.len(),
        ensures
            final(self).model@ == old(self).model@,
            raw_vec_capacity(final(self)) >= cap as nat,
            raw_vec_capacity(final(self)) <= raw_vec_capacity(old(self)),
            forall|prefix_len: usize| prefix_len <= cap ==>
                raw_vec_initialized_seq(final(self), prefix_len) ==
                    raw_vec_initialized_seq(old(self), prefix_len),
        no_unwind
    {
        let ghost old_cap = self.cap;
        if self.cap > cap {
            self.cap = cap;
        }
        proof {
            assert(self.model@ == old(self).model@);
            if old_cap > cap {
                assert(self.cap == cap);
            } else {
                assert(self.cap == old_cap);
                assert(cap <= old_cap);
            }
            assert(self.cap >= cap);
            assert(self.cap <= old_cap);
            assert(raw_vec_capacity(self) >= cap as nat);
            assert(raw_vec_capacity(self) <= raw_vec_capacity(old(self)));
            assert forall|prefix_len: usize| prefix_len <= cap implies
                raw_vec_initialized_seq(self, prefix_len) ==
                    raw_vec_initialized_seq(old(self), prefix_len)
            by {
                assert(raw_vec_initialized_seq(self, prefix_len).len() ==
                    raw_vec_initialized_seq(old(self), prefix_len).len());
                assert forall|i: int|
                    0 <= i < raw_vec_initialized_seq(self, prefix_len).len()
                    implies raw_vec_initialized_seq(self, prefix_len)[i] ==
                        raw_vec_initialized_seq(old(self), prefix_len)[i]
                by {
                    assert(i < prefix_len as nat);
                    assert(i < cap as nat);
                    assert(i < old(self).model@.len());
                }
                assert(raw_vec_initialized_seq(self, prefix_len) =~=
                    raw_vec_initialized_seq(old(self), prefix_len));
            }
        }
    }
}

impl<T, A: Allocator> Vec<T, A> {
    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool {
        self.len as nat <= raw_vec_capacity(&self.buf)
            && raw_vec_capacity(&self.buf) <= self.buf.model@.len()
    }

    fn capacity(&self) -> (capacity: usize)
        ensures
            capacity as nat == self.spec_capacity(),
            self.len as nat <= self.spec_capacity(),
    {
        let capacity = self.buf.capacity();
        proof {
            use_type_invariant(self);
            assert(self.len as nat <= raw_vec_capacity(&self.buf));
            assert(self.spec_capacity() == raw_vec_capacity(&self.buf));
        }
        capacity
    }

    pub fn shrink_to_fit(&mut self)
        ensures
            final(self)@ == old(self)@,
            final(self).spec_capacity() >= old(self)@.len(),
            final(self).spec_capacity() <= old(self).spec_capacity(),
    {
        let ghost source = self@;
        let ghost source_len = self.len;
        let ghost source_capacity = self.spec_capacity();
        proof {
            use_type_invariant(&*self);
            assert(self.len as nat <= raw_vec_capacity(&self.buf));
            assert(self.spec_capacity() == raw_vec_capacity(&self.buf));
            assert(raw_vec_capacity(&self.buf) <= self.buf.model@.len());
            assert(source.len() == source_len as nat);
            assert(source_len as nat <= source_capacity);
        }
        if self.capacity() > self.len {
            proof {
                assert(self.len == source_len);
                assert(self.spec_capacity() == source_capacity);
                assert(raw_vec_capacity(&self.buf) == source_capacity);
                assert(self.len as nat <= raw_vec_capacity(&self.buf));
                assert(self.len as nat <= self.buf.model@.len());
            }
            self.buf.shrink_to_fit(self.len);
            proof {
                assert(self.len == source_len);
                assert(source_len <= self.len);
                assert(raw_vec_initialized_seq(&self.buf, source_len) == source);
                assert(self@ == source);
                assert(self.spec_capacity() >= source_len as nat);
                assert(self.spec_capacity() <= source_capacity);
            }
        } else {
            proof {
                assert(self@ == source);
                assert(self.spec_capacity() == source_capacity);
                assert(self.spec_capacity() >= source_len as nat);
            }
        }
    }

    pub fn into_boxed_slice(self) -> (ret: BoxedSlice<T, A>)
        ensures
            boxed_slice_view::<T, A>(ret) == self@,
            boxed_slice_capacity::<T, A>(ret) == self@.len(),
    {
        let ghost source_view = self@;
        let mut this = self;
        unsafe {
            this.shrink_to_fit();
            let me = ManuallyDrop::new(this);
            let buf = ptr::read(&me.buf);
            let len = me.len();
            proof {
                assert(len == me.len);
                assert(raw_vec_initialized_seq(&me.buf, me.len) == source_view);
                assert(raw_vec_initialized_seq(&buf, len) == source_view);
                assert(len as nat <= raw_vec_capacity(&buf));
            }
            buf.into_box(len).assume_init()
        }
    }
}

impl<T, A: Allocator> ManuallyDrop<T, A> {
    fn new(vec: Vec<T, A>) -> (me: Self)
        ensures
            raw_vec_initialized_seq(&me.buf, me.len) == vec@,
            raw_vec_capacity(&me.buf) == vec.spec_capacity(),
            me.len as nat == vec@.len(),
    {
        let ghost source_view = vec@;
        let ghost source_capacity = vec.spec_capacity();
        let len = vec.len;
        let me = ManuallyDrop { buf: vec.buf, len };
        proof {
            assert(me.len == len);
            assert(raw_vec_initialized_seq(&me.buf, me.len) =~= source_view);
            assert(raw_vec_capacity(&me.buf) == source_capacity);
            assert(me.len as nat == source_view.len());
        }
        me
    }

    fn len(&self) -> (len: usize)
        ensures
            len == self.len,
            len as nat == raw_vec_initialized_seq(&self.buf, self.len).len(),
    {
        self.len
    }
}

pub mod ptr {
    use super::*;

    pub unsafe fn read<T, A: Allocator>(src: &RawVec<T, A>) -> (buf: RawVec<T, A>)
        ensures
            forall|len: usize| raw_vec_initialized_seq(&buf, len) == raw_vec_initialized_seq(src, len),
            raw_vec_capacity(&buf) == raw_vec_capacity(src),
    {
        RawVec { cap: src.cap, model: Ghost(src.model@), _marker_t: PhantomData, _marker_a: PhantomData }
    }
}

impl<T, A: Allocator> RawVec<T, A> {
    pub unsafe fn into_box(self, len: usize) -> (boxed: BoxedMaybeUninitSlice<T, A>)
        requires
            len as nat == raw_vec_initialized_seq(&self, len).len(),
            len as nat <= raw_vec_capacity(&self),
        ensures
            maybe_uninit_box_view(&boxed) == raw_vec_initialized_seq(&self, len),
            maybe_uninit_box_capacity(&boxed) == len as nat,
    {
        let ghost view = raw_vec_initialized_seq(&self, len);
        let ghost capacity = len as nat;
        BoxedMaybeUninitSlice {
            view: Ghost(view),
            capacity: Ghost(capacity),
            _marker_t: PhantomData,
            _marker_a: PhantomData,
        }
    }
}

impl<T, A: Allocator> BoxedMaybeUninitSlice<T, A> {
    pub unsafe fn assume_init(self) -> (boxed: BoxedSlice<T, A>)
        ensures
            boxed_slice_view::<T, A>(boxed) == maybe_uninit_box_view(&self),
            boxed_slice_capacity::<T, A>(boxed) == maybe_uninit_box_capacity(&self),
    {
        let ghost view = maybe_uninit_box_view(&self);
        let ghost capacity = maybe_uninit_box_capacity(&self);
        BoxedSlice {
            view: Ghost(view),
            capacity: Ghost(capacity),
            _marker_t: PhantomData,
            _marker_a: PhantomData,
        }
    }
}

}
