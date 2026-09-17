// Additional Rust standard-library Vec specifications generated from the
// independently audited zero-UF corpus. Existing vstd Vec specifications remain
// in `vec.rs`; this module contains the previously uncovered stable targets.
use super::super::prelude::*;

use alloc::vec::{Drain, ExtractIf, IntoIter, Vec};

use verus as verus_;

verus_! {

#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExDrain<'a, T, A>(Drain<'a, T, A>)
where
    T: 'a,
    A: core::alloc::Allocator,
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(F)]
#[verifier::reject_recursive_types(A)]
pub struct ExExtractIf<'a, T, F, A: core::alloc::Allocator>(ExtractIf<'a, T, F, A>);

pub assume_specification<'a, 'b, T, A: core::alloc::Allocator>[ Drain::<'a, T, A>::as_slice ](
    drain: &'b Drain<'a, T, A>,
) -> (ret: &'b [T])
;

pub assume_specification<T, A: core::alloc::Allocator>[ IntoIter::<T, A>::as_mut_slice ](
    iter: &mut IntoIter<T, A>,
) -> (ret: &mut [T])

    ensures
        final(ret)@.len() == ret@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator>[ IntoIter::<T, A>::as_slice ](
    iter: &IntoIter<T, A>,
) -> (ret: &[T])
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::as_mut_ptr ](
    vec: &mut Vec<T, A>,
) -> (ptr: *mut T)

    ensures
        ptr.addr() % core::mem::align_of::<T>() == 0,
        final(vec)@ == old(vec)@,
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::as_ptr ](
    vec: &Vec<T, A>,
) -> (ptr: *const T)

    ensures
        ptr.addr() % core::mem::align_of::<T>() == 0,
;

pub assume_specification<T: core::cmp::PartialEq, A: core::alloc::Allocator>[ Vec::<T, A>::dedup ](
    vec: &mut Vec<T, A>,
)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut(&mut T, &mut T) -> bool>[
    Vec::<T, A>::dedup_by::<F>
](
    vec: &mut Vec<T, A>,
    same_bucket: F,
)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut(&mut T) -> K, K: core::cmp::PartialEq>[
    Vec::<T, A>::dedup_by_key::<F, K>
](
    vec: &mut Vec<T, A>,
    key: F,
)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, R: core::ops::RangeBounds<usize>>[
    Vec::<T, A>::drain::<R>
](
    vec: &mut Vec<T, A>,
    range: R,
) -> (drain: Drain<'_, T, A>)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T: core::clone::Clone, A: core::alloc::Allocator, R: core::ops::RangeBounds<usize>>[
    Vec::<T, A>::extend_from_within::<R>
](
    vec: &mut Vec<T, A>,
    src: R,
)

    ensures
        final(vec)@.len() >= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut(&mut T) -> bool, R: core::ops::RangeBounds<usize>>[
    Vec::<T, A>::extract_if::<F, R>
](
    vec: &mut Vec<T, A>,
    range: R,
    filter: F,
) -> (iter: ExtractIf<'_, T, F, A>)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T>[ Vec::<T>::from_raw_parts ](
    ptr: *mut T,
    length: usize,
    capacity: usize,
) -> (vec: Vec<T>)

    requires
        length == 0,
        capacity == 0,
        ptr.addr() != 0,
        ptr.addr() % core::mem::align_of::<T>() == 0,
    ensures
        vec@.len() == length,
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::insert_mut ](
    vec: &mut Vec<T, A>,
    index: usize,
    element: T,
) -> (ret: &mut T)
    requires
        index <= old(vec)@.len(),
    ensures
        *ret == element,
        final(vec)@ == old(vec)@.insert(index as int, *final(ret)),
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::into_boxed_slice ](
    vec: Vec<T, A>,
) -> (ret: alloc::boxed::Box<[T], A>)

    ensures
        ret@ == vec@,
;

pub assume_specification<T, A: core::alloc::Allocator, const N: usize>[
    Vec::<[T; N], A>::into_flattened
](
    vec: Vec<[T; N], A>,
) -> (ret: Vec<T, A>)

    requires
        core::mem::size_of::<T>() != 0 || vec@.len() * N <= usize::MAX,
    ensures
        ret@.len() == vec@.len() * N,
        forall|i: int, j: int|
            #![trigger ret@[i * N as int + j]]
            0 <= i < vec@.len() && 0 <= j < N
                ==> ret@[i * N as int + j] == vec@[i]@[j],
;

pub assume_specification<T>[ Vec::<T>::into_raw_parts ](
    vec: Vec<T>,
) -> (parts: (*mut T, usize, usize))

    ensures
        parts.1 == vec@.len(),
        parts.1 <= parts.2,
;

pub assume_specification<'a, T, A: core::alloc::Allocator + 'a>[ Vec::<T, A>::leak ](
    vec: Vec<T, A>,
) -> (ret: &'a mut [T])
    ensures
        ret@ == vec@,
        final(ret)@.len() == vec@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, P: core::ops::FnOnce(&mut T) -> bool>[
    Vec::<T, A>::pop_if
](
    vec: &mut Vec<T, A>,
    predicate: P,
) -> (ret: Option<T>)

    ensures
        old(vec)@.len() == 0 ==> ret.is_none() && final(vec)@ == old(vec)@,
        old(vec)@.len() != 0 ==> {
            &&& (ret.is_none() ==> final(vec)@.len() == old(vec)@.len())
            &&& (ret.is_some() ==> final(vec)@.len() + 1 == old(vec)@.len())
        },
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::push_mut ](
    vec: &mut Vec<T, A>,
    value: T,
) -> (ret: &mut T)
    ensures
        *ret == value,
        final(vec)@ == old(vec)@.push(*final(ret)),
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut() -> T>[
    Vec::<T, A>::resize_with::<F>
](
    vec: &mut Vec<T, A>,
    new_len: usize,
    f: F,
)

    ensures
        final(vec)@.len() == new_len,
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut(&T) -> bool>[
    Vec::<T, A>::retain::<F>
](
    vec: &mut Vec<T, A>,
    f: F,
)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator, F: core::ops::FnMut(&mut T) -> bool>[
    Vec::<T, A>::retain_mut::<F>
](
    vec: &mut Vec<T, A>,
    f: F,
)

    ensures
        final(vec)@.len() <= old(vec)@.len(),
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::set_len ](
    vec: &mut Vec<T, A>,
    new_len: usize,
)

    requires
        new_len <= old(vec)@.len(),
    ensures
        final(vec)@ == old(vec)@.subrange(0, new_len as int),
;

pub assume_specification<T, A: core::alloc::Allocator>[ Vec::<T, A>::spare_capacity_mut ](
    vec: &mut Vec<T, A>,
) -> (ret: &mut [core::mem::MaybeUninit<T>])

    ensures
        final(vec)@ == old(vec)@,
;

} // verus!
