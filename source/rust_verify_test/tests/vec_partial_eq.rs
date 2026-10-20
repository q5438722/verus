#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_vec_partial_eq_specs verus_code! {
        use core::alloc::Allocator;
        use std::borrow::Cow;
        use vstd::prelude::*;
        use vstd::std_specs::cmp::PartialEqSpec;
        use vstd::std_specs::vec::partial_eq::cow_seq;

        fn binding_0<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &Vec<T, A>, right: &&[U]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            &[U],
        >>::eq(left, right)
        }

        fn binding_1<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &Vec<T, A>, right: &&[U]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            &[U],
        >>::ne(left, right)
        }

        fn binding_2<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &Vec<T, A>, right: &&mut [U]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            &mut [U],
        >>::eq(left, right)
        }

        fn binding_3<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &Vec<T, A>, right: &&mut [U]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            &mut [U],
        >>::ne(left, right)
        }

        fn binding_4<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &&'spec0 [T], right: &Vec<U, A>) -> (result: bool)
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
        {
            <&'spec0 [T] as PartialEq<
            Vec<U, A>,
        >>::eq(left, right)
        }

        fn binding_5<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &&'spec0 [T], right: &Vec<U, A>) -> (result: bool)
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
        {
            <&'spec0 [T] as PartialEq<
            Vec<U, A>,
        >>::ne(left, right)
        }

        fn binding_6<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &&'spec0 mut [T], right: &Vec<U, A>) -> (result: bool)
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
        {
            <&'spec0 mut [T] as PartialEq<
            Vec<U, A>,
        >>::eq(left, right)
        }

        fn binding_7<'spec0, T: PartialEq<U>, U, A: Allocator>(left: &&'spec0 mut [T], right: &Vec<U, A>) -> (result: bool)
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
        {
            <&'spec0 mut [T] as PartialEq<
            Vec<U, A>,
        >>::ne(left, right)
        }

        fn binding_8<T: PartialEq<U>, U, A: Allocator>(
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
        {
            <Vec<T, A> as PartialEq<[U]>>::eq(left, right)
        }

        fn binding_9<T: PartialEq<U>, U, A: Allocator>(
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
        {
            <Vec<T, A> as PartialEq<[U]>>::ne(left, right)
        }

        fn binding_10<T: PartialEq<U>, U, A: Allocator>(
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
        {
            <[T] as PartialEq<Vec<U, A>>>::eq(left, right)
        }

        fn binding_11<T: PartialEq<U>, U, A: Allocator>(
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
        {
            <[T] as PartialEq<Vec<U, A>>>::ne(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_12<'spec0, T: PartialEq<U> + Clone, U, A: Allocator>(left: &Cow<'spec0, [T]>, right: &Vec<U, A>) -> (result: bool)
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
        {
            <Cow<
            'spec0,
            [T],
        > as PartialEq<Vec<U, A>>>::eq(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_13<'spec0, T: PartialEq<U> + Clone, U, A: Allocator>(left: &Cow<'spec0, [T]>, right: &Vec<U, A>) -> (result: bool)
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
        {
            <Cow<
            'spec0,
            [T],
        > as PartialEq<Vec<U, A>>>::ne(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_14<'spec0, 'spec1, T: PartialEq<U> + Clone, U>(left: &Cow<'spec1, [T]>, right: &&[U]) -> (result: bool)
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
        {
            <Cow<
            'spec1,
            [T],
        > as PartialEq<&[U]>>::eq(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_15<'spec0, 'spec1, T: PartialEq<U> + Clone, U>(left: &Cow<'spec1, [T]>, right: &&[U]) -> (result: bool)
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
        {
            <Cow<
            'spec1,
            [T],
        > as PartialEq<&[U]>>::ne(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_16<'spec0, 'spec1, T: PartialEq<U> + Clone, U>(left: &Cow<'spec1, [T]>, right: &&mut [U]) -> (result: bool)
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
        {
            <Cow<
            'spec1,
            [T],
        > as PartialEq<&mut [U]>>::eq(left, right)
        }

        #[cfg(not(no_global_oom_handling))]
        fn binding_17<'spec0, 'spec1, T: PartialEq<U> + Clone, U>(left: &Cow<'spec1, [T]>, right: &&mut [U]) -> (result: bool)
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
        {
            <Cow<
            'spec1,
            [T],
        > as PartialEq<&mut [U]>>::ne(left, right)
        }

        fn binding_18<T: PartialEq<U>, U, A: Allocator, const N: usize>(left: &Vec<T, A>, right: &[U; N]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            [U; N],
        >>::eq(left, right)
        }

        fn binding_19<T: PartialEq<U>, U, A: Allocator, const N: usize>(left: &Vec<T, A>, right: &[U; N]) -> (result: bool)
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
        {
            <Vec<T, A> as PartialEq<
            [U; N],
        >>::ne(left, right)
        }

        fn binding_20<'spec0, T: PartialEq<U>, U, A: Allocator, const N: usize>(left: &Vec<T, A>, right: &&[U; N]) -> (result: bool)
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
        {
            <Vec<
            T,
            A,
        > as PartialEq<&[U; N]>>::eq(left, right)
        }

        fn binding_21<'spec0, T: PartialEq<U>, U, A: Allocator, const N: usize>(left: &Vec<T, A>, right: &&[U; N]) -> (result: bool)
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
        {
            <Vec<
            T,
            A,
        > as PartialEq<&[U; N]>>::ne(left, right)
        }

    } => Ok(())
}
