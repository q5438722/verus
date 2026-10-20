#[cfg(not(no_global_oom_handling))]
use alloc::borrow::Cow;
use alloc::vec::Vec;
use core::alloc::Allocator;

use crate::prelude::*;
use crate::std_specs::cmp::PartialEqSpec;

use verus as verus_skip_verusfmt;
verus_skip_verusfmt! {

#[cfg(not(no_global_oom_handling))]
pub open spec fn cow_seq<'a, T: Clone>(cow: &Cow<'a, [T]>) -> Seq<T> {
    match cow {
        Cow::Borrowed(contents) => contents@,
        Cow::Owned(contents) => contents@,
    }
}

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<
    &[U],
>>::eq ](left: &Vec<T, A>, right: &&[U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<
    &[U],
>>::ne ](left: &Vec<T, A>, right: &&[U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<
    &mut [U],
>>::eq ](left: &Vec<T, A>, right: &&mut [U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = old(*right)@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<
    &mut [U],
>>::ne ](left: &Vec<T, A>, right: &&mut [U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = old(*right)@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <&'spec0 [T] as PartialEq<
    Vec<U, A>,
>>::eq ](left: &&'spec0 [T], right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <&'spec0 [T] as PartialEq<
    Vec<U, A>,
>>::ne ](left: &&'spec0 [T], right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <&'spec0 mut [T] as PartialEq<
    Vec<U, A>,
>>::eq ](left: &&'spec0 mut [T], right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = old(*left)@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator>[ <&'spec0 mut [T] as PartialEq<
    Vec<U, A>,
>>::ne ](left: &&'spec0 mut [T], right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = old(*left)@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<[U]>>::eq ](
    left: &Vec<T, A>,
    right: &[U],
) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator>[ <Vec<T, A> as PartialEq<[U]>>::ne ](
    left: &Vec<T, A>,
    right: &[U],
) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator>[ <[T] as PartialEq<Vec<U, A>>>::eq ](
    left: &[T],
    right: &Vec<U, A>,
) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator>[ <[T] as PartialEq<Vec<U, A>>>::ne ](
    left: &[T],
    right: &Vec<U, A>,
) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, T: PartialEq<U> + Clone, U, A: Allocator>[ <Cow<
    'spec0,
    [T],
> as PartialEq<Vec<U, A>>>::eq ](left: &Cow<'spec0, [T]>, right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, T: PartialEq<U> + Clone, U, A: Allocator>[ <Cow<
    'spec0,
    [T],
> as PartialEq<Vec<U, A>>>::ne ](left: &Cow<'spec0, [T]>, right: &Vec<U, A>) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, 'spec1, T: PartialEq<U> + Clone, U>[ <Cow<
    'spec1,
    [T],
> as PartialEq<&[U]>>::eq ](left: &Cow<'spec1, [T]>, right: &&[U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, 'spec1, T: PartialEq<U> + Clone, U>[ <Cow<
    'spec1,
    [T],
> as PartialEq<&[U]>>::ne ](left: &Cow<'spec1, [T]>, right: &&[U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, 'spec1, T: PartialEq<U> + Clone, U>[ <Cow<
    'spec1,
    [T],
> as PartialEq<&mut [U]>>::eq ](left: &Cow<'spec1, [T]>, right: &&mut [U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = old(*right)@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

#[cfg(not(no_global_oom_handling))]
pub assume_specification<'spec0, 'spec1, T: PartialEq<U> + Clone, U>[ <Cow<
    'spec1,
    [T],
> as PartialEq<&mut [U]>>::ne ](left: &Cow<'spec1, [T]>, right: &&mut [U]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = cow_seq(left);
            let right_contents = old(*right)@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator, const N: usize>[ <Vec<T, A> as PartialEq<
    [U; N],
>>::eq ](left: &Vec<T, A>, right: &[U; N]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<T: PartialEq<U>, U, A: Allocator, const N: usize>[ <Vec<T, A> as PartialEq<
    [U; N],
>>::ne ](left: &Vec<T, A>, right: &[U; N]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator, const N: usize>[ <Vec<
    T,
    A,
> as PartialEq<&[U; N]>>::eq ](left: &Vec<T, A>, right: &&[U; N]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == (left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

pub assume_specification<'spec0, T: PartialEq<U>, U, A: Allocator, const N: usize>[ <Vec<
    T,
    A,
> as PartialEq<&[U; N]>>::ne ](left: &Vec<T, A>, right: &&[U; N]) -> (result: bool)
    ensures
        <T as PartialEqSpec<U>>::obeys_eq_spec() ==> {
            let left_contents = left@;
            let right_contents = right@;
            result == !(left_contents.len() == right_contents.len() && forall|i: int|
                #![trigger left_contents[i]]
                0 <= i < left_contents.len() ==> <T as PartialEqSpec<U>>::eq_spec(
                    &left_contents[i],
                    &right_contents[i],
                ))
        },
;

}
