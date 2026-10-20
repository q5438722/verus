#![feature(rustc_private)]
#![allow(unused_imports)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_slice_generated_submodules verus_code! {
        mod array_slices {
            use core::slice::*;
            use vstd::prelude::*;
            use vstd::std_specs::slice::arrays::array_slices::*;

            fn binding_0<T, const N: usize>(slice: &[T]) -> (result: Option<
                &[T; N],
            >)
                ensures
                    match result {
                        Some(array) => slice@.len() == N && array@ == slice@,
                        None => slice@.len() != N,
                    },
            {
                <[T]>::as_array(slice)
            }

            fn binding_1<T, const N: usize>(slice: &[T]) -> (result: Option<
                &[T; N],
            >)
                ensures
                    match result {
                        Some(array) => N <= slice@.len() && array@ == slice@.subrange(0, N as int),
                        None => slice@.len() < N,
                    },
            {
                <[T]>::first_chunk(slice)
            }

            fn binding_2<T, const N: usize>(slice: &[T]) -> (result: Option<
                &[T; N],
            >)
                ensures
                    match result {
                        Some(array) => N <= slice@.len() && array@ == slice@.subrange(
                            slice@.len() - N,
                            slice@.len() as int,
                        ),
                        None => slice@.len() < N,
                    },
            {
                <[T]>::last_chunk(slice)
            }

            fn binding_3<T, const N: usize>(slice: &[T]) -> (result:
                Option<(&[T; N], &[T])>)
                ensures
                    match result {
                        Some((array, tail)) => N <= slice@.len() && array@ == slice@.subrange(0, N as int)
                            && tail@ == slice@.subrange(N as int, slice@.len() as int),
                        None => slice@.len() < N,
                    },
            {
                <[T]>::split_first_chunk(slice)
            }

            fn binding_4<T, const N: usize>(slice: &[T]) -> (result:
                Option<(&[T], &[T; N])>)
                ensures
                    match result {
                        Some((init, array)) => N <= slice@.len() && init@ == slice@.subrange(
                            0,
                            slice@.len() - N,
                        ) && array@ == slice@.subrange(slice@.len() - N, slice@.len() as int),
                        None => slice@.len() < N,
                    },
            {
                <[T]>::split_last_chunk(slice)
            }

            fn binding_5<T, const N: usize>(slice: &mut [T]) -> (result:
                Option<&mut [T; N]>)
                ensures
                    match result {
                        Some(array) => old(slice)@.len() == N && array@ == old(slice)@ && final(array)@.len()
                            == N && final(slice)@ == final(array)@,
                        None => old(slice)@.len() != N && final(slice)@ == old(slice)@,
                    },
            {
                <[T]>::as_mut_array(slice)
            }

            fn binding_6<T, const N: usize>(slice: &mut [T]) -> (result:
                Option<&mut [T; N]>)
                ensures
                    match result {
                        Some(array) => N <= old(slice)@.len() && array@ == old(slice)@.subrange(0, N as int)
                            && final(array)@.len() == N && final(slice)@ == final(array)@ + old(
                            slice,
                        )@.subrange(N as int, old(slice)@.len() as int),
                        None => old(slice)@.len() < N && final(slice)@ == old(slice)@,
                    },
            {
                <[T]>::first_chunk_mut(slice)
            }

            fn binding_7<T, const N: usize>(slice: &mut [T]) -> (result:
                Option<&mut [T; N]>)
                ensures
                    match result {
                        Some(array) => N <= old(slice)@.len() && array@ == old(slice)@.subrange(
                            old(slice)@.len() - N,
                            old(slice)@.len() as int,
                        ) && final(array)@.len() == N && final(slice)@ == old(slice)@.subrange(
                            0,
                            old(slice)@.len() - N,
                        ) + final(array)@,
                        None => old(slice)@.len() < N && final(slice)@ == old(slice)@,
                    },
            {
                <[T]>::last_chunk_mut(slice)
            }

            fn binding_8<T, const N: usize>(
                slice: &mut [T],
            ) -> (result: Option<(&mut [T; N], &mut [T])>)
                ensures
                    match result {
                        Some((array, tail)) => N <= old(slice)@.len() && array@ == old(slice)@.subrange(
                            0,
                            N as int,
                        ) && tail@ == old(slice)@.subrange(N as int, old(slice)@.len() as int)
                            && final(array)@.len() == N && final(tail)@.len() == old(slice)@.len() - N
                            && final(slice)@ == final(array)@ + final(tail)@,
                        None => old(slice)@.len() < N && final(slice)@ == old(slice)@,
                    },
            {
                <[T]>::split_first_chunk_mut(slice)
            }

            fn binding_9<T, const N: usize>(
                slice: &mut [T],
            ) -> (result: Option<(&mut [T], &mut [T; N])>)
                ensures
                    match result {
                        Some((init, array)) => N <= old(slice)@.len() && init@ == old(slice)@.subrange(
                            0,
                            old(slice)@.len() - N,
                        ) && array@ == old(slice)@.subrange(old(slice)@.len() - N, old(slice)@.len() as int)
                            && final(init)@.len() == old(slice)@.len() - N && final(array)@.len() == N
                            && final(slice)@ == final(init)@ + final(array)@,
                        None => old(slice)@.len() < N && final(slice)@ == old(slice)@,
                    },
            {
                <[T]>::split_last_chunk_mut(slice)
            }

            fn binding_10<T, const N: usize>(slice: &[T]) -> (result:
                &[[T; N]])
                requires
                    N > 0,
                    slice@.len() % (N as nat) == 0,
                ensures
                    row_views(result@) == reshape(slice@, slice@.len() / (N as nat), N as nat),
            {
                unsafe { <[T]>::as_chunks_unchecked(slice) }
            }

            fn binding_11<T, const N: usize>(slice: &[T]) -> (result: (
                &[[T; N]],
                &[T],
            ))
                ensures
                    N > 0,
                    row_views(result.0@) == reshape(
                        slice@.subrange(0, (slice@.len() / (N as nat) * N) as int),
                        slice@.len() / (N as nat),
                        N as nat,
                    ),
                    result.1@ == slice@.subrange((slice@.len() / (N as nat) * N) as int, slice@.len() as int),
            {
                <[T]>::as_chunks(slice)
            }

            fn binding_12<T, const N: usize>(slice: &[T]) -> (result: (
                &[T],
                &[[T; N]],
            ))
                ensures
                    N > 0,
                    result.0@ == slice@.subrange(0, slice@.len() - slice@.len() / (N as nat) * N),
                    row_views(result.1@) == reshape(
                        slice@.subrange(slice@.len() - slice@.len() / (N as nat) * N, slice@.len() as int),
                        slice@.len() / (N as nat),
                        N as nat,
                    ),
            {
                <[T]>::as_rchunks(slice)
            }

            fn binding_13<T, const N: usize>(
                slice: &mut [T],
            ) -> (result: &mut [[T; N]])
                requires
                    N > 0,
                    old(slice)@.len() % (N as nat) == 0,
                ensures
                    row_views(result@) == reshape(
                        old(slice)@,
                        old(slice)@.len() / (N as nat),
                        N as nat,
                    ),
                    result@.len() == old(slice)@.len() / (N as nat),
                    final(result)@.len() == old(slice)@.len() / (N as nat),
                    final(slice)@.len() == old(slice)@.len(),
                    final(slice)@ == row_views(final(result)@).flatten(),
            {
                unsafe { <[T]>::as_chunks_unchecked_mut(slice) }
            }

            fn binding_14<T, const N: usize>(slice: &mut [T]) -> (result: (
                &mut [[T; N]],
                &mut [T],
            ))
                ensures
                    N > 0,
                    row_views(result.0@) == reshape(
                        old(slice)@.subrange(0, (old(slice)@.len() / (N as nat) * N) as int),
                        old(slice)@.len() / (N as nat),
                        N as nat,
                    ),
                    result.1@ == old(slice)@.subrange(
                        (old(slice)@.len() / (N as nat) * N) as int,
                        old(slice)@.len() as int,
                    ),
                    result.0@.len() == old(slice)@.len() / (N as nat),
                    result.1@.len() == old(slice)@.len() % (N as nat),
                    final(result.0)@.len() == old(slice)@.len() / (N as nat),
                    final(result.1)@.len() == old(slice)@.len() % (N as nat),
                    final(slice)@.len() == old(slice)@.len(),
                    final(slice)@ == row_views(final(result.0)@).flatten() + final(result.1)@,
            {
                <[T]>::as_chunks_mut(slice)
            }

            fn binding_15<T, const N: usize>(slice: &mut [T]) -> (result: (
                &mut [T],
                &mut [[T; N]],
            ))
                ensures
                    N > 0,
                    result.0@ == old(slice)@.subrange(
                        0,
                        old(slice)@.len() - old(slice)@.len() / (N as nat) * N,
                    ),
                    row_views(result.1@) == reshape(
                        old(slice)@.subrange(
                            old(slice)@.len() - old(slice)@.len() / (N as nat) * N,
                            old(slice)@.len() as int,
                        ),
                        old(slice)@.len() / (N as nat),
                        N as nat,
                    ),
                    result.0@.len() == old(slice)@.len() % (N as nat),
                    result.1@.len() == old(slice)@.len() / (N as nat),
                    final(result.0)@.len() == old(slice)@.len() % (N as nat),
                    final(result.1)@.len() == old(slice)@.len() / (N as nat),
                    final(slice)@.len() == old(slice)@.len(),
                    final(slice)@ == final(result.0)@ + row_views(final(result.1)@).flatten(),
            {
                <[T]>::as_rchunks_mut(slice)
            }

            fn binding_16<T, const N: usize>(
                slice: &[[T; N]],
            ) -> (result: &[T])
                ensures
                    result@ == row_views(slice@).flatten(),
            {
                <[[T; N]]>::as_flattened(slice)
            }

            fn binding_17<T, const N: usize>(
                slice: &mut [[T; N]],
            ) -> (result: &mut [T])
                ensures
                    result@ == row_views(old(slice)@).flatten(),
                    result@.len() == old(slice)@.len() * N,
                    final(result)@.len() == old(slice)@.len() * N,
                    final(slice)@.len() == old(slice)@.len(),
                    row_views(final(slice)@) == reshape(
                        final(result)@,
                        old(slice)@.len(),
                        N as nat,
                    ),
            {
                <[[T; N]]>::as_flattened_mut(slice)
            }

        }

        mod array_windows {
            use core::slice::*;
            use vstd::prelude::*;
            use vstd::std_specs::iter::IteratorSpec;
            use vstd::std_specs::slice::arrays::array_windows::*;

            fn binding_0<'a, T, const N: usize>(
                iter: &ArrayWindows<'a, T, N>,
            ) -> (result: ArrayWindows<'a, T, N>)
                ensures
                    result == *iter,
                    result.remaining() == iter.remaining(),
                    result.obeys_prophetic_iter_laws() == iter.obeys_prophetic_iter_laws(),
                    result.will_return_none() == iter.will_return_none(),
                    result.decrease() == iter.decrease(),
            {
                <ArrayWindows<'a, T, N> as Clone>::clone(iter)
            }

            fn binding_1<'a, T, const N: usize>(slice: &'a [T]) -> (result:
                ArrayWindows<'a, T, N>)
                ensures
                    N > 0,
                    result@ == slice@,
                    result.remaining() == remaining::<T, N>(result@),
                    item_values(result.remaining()) == values::<T, N>(result@),
                    result.obeys_prophetic_iter_laws(),
                    result.will_return_none(),
                    result.decrease() is Some,
            {
                <[T]>::array_windows(slice)
            }

            fn binding_2<'a, T, const N: usize>(
                iter: &mut ArrayWindows<'a, T, N>,
            ) -> (result: Option<<ArrayWindows<'a, T, N> as Iterator>::Item>)
                ensures
                    valid::<T, N>(old(iter)@),
                    valid::<T, N>(final(iter)@),
                    if N <= old(iter)@.len() {
                        result is Some && result.unwrap()@ == old(iter)@.subrange(0, N as int) && final(iter)@
                            == old(iter)@.drop_first()
                    } else {
                        result is None && final(iter)@ == old(iter)@
                    },
            {
                <ArrayWindows<'a, T, N> as Iterator>::next(iter)
            }

            fn binding_3<'a, T, const N: usize>(iter: &mut ArrayWindows<'a, T, N>) -> (result: Option<
                &'a [T; N],
            >)
                ensures
                    valid::<T, N>(old(iter)@),
                    valid::<T, N>(final(iter)@),
                    if N <= old(iter)@.len() {
                        result is Some && result.unwrap()@ == old(iter)@.subrange(
                            old(iter)@.len() - N,
                            old(iter)@.len() as int,
                        ) && final(iter)@ == old(iter)@.drop_last()
                    } else {
                        result is None && final(iter)@ == old(iter)@
                    },
            {
                <ArrayWindows<
                'a,
                T,
                N,
            > as DoubleEndedIterator>::next_back(iter)
            }

            fn binding_4<'a, T, const N: usize>(
                iter: &mut ArrayWindows<'a, T, N>,
                n: usize,
            ) -> (result: Option<<ArrayWindows<'a, T, N> as Iterator>::Item>)
                ensures
                    valid::<T, N>(old(iter)@),
                    valid::<T, N>(final(iter)@),
                    ({
                        let selected = skip_front(old(iter)@, n);
                        if N <= selected.len() {
                            result is Some && result.unwrap()@ == selected.subrange(0, N as int) && final(iter)@
                                == selected.drop_first()
                        } else {
                            result is None && final(iter)@ == selected
                        }
                    }),
                    old(iter).remaining() == remaining::<T, N>(old(iter)@),
                    item_values(old(iter).remaining()) == values::<T, N>(old(iter)@),
                    old(iter).obeys_prophetic_iter_laws(),
                    old(iter).will_return_none(),
                    old(iter).decrease() is Some,
                    IteratorSpec::remaining(final(iter)) == remaining::<T, N>(final(iter)@),
                    item_values(IteratorSpec::remaining(final(iter))) == values::<T, N>(final(iter)@),
                    IteratorSpec::obeys_prophetic_iter_laws(final(iter)),
                    IteratorSpec::will_return_none(final(iter)),
                    IteratorSpec::decrease(final(iter)) is Some,
            {
                <ArrayWindows<'a, T, N> as Iterator>::nth(iter, n)
            }

            fn binding_5<'a, T, const N: usize>(iter: &mut ArrayWindows<'a, T, N>, n: usize) -> (result:
                Option<&'a [T; N]>)
                ensures
                    valid::<T, N>(old(iter)@),
                    valid::<T, N>(final(iter)@),
                    ({
                        let selected = skip_back(old(iter)@, n);
                        if N <= selected.len() {
                            result is Some && result.unwrap()@ == selected.subrange(
                                selected.len() - N,
                                selected.len() as int,
                            ) && final(iter)@ == selected.drop_last()
                        } else {
                            result is None && final(iter)@ == selected
                        }
                    }),
                    old(iter).remaining() == remaining::<T, N>(old(iter)@),
                    item_values(old(iter).remaining()) == values::<T, N>(old(iter)@),
                    old(iter).obeys_prophetic_iter_laws(),
                    old(iter).will_return_none(),
                    old(iter).decrease() is Some,
                    IteratorSpec::remaining(final(iter)) == remaining::<T, N>(final(iter)@),
                    item_values(IteratorSpec::remaining(final(iter))) == values::<T, N>(final(iter)@),
                    IteratorSpec::obeys_prophetic_iter_laws(final(iter)),
                    IteratorSpec::will_return_none(final(iter)),
                    IteratorSpec::decrease(final(iter)) is Some,
            {
                <ArrayWindows<
                'a,
                T,
                N,
            > as DoubleEndedIterator>::nth_back(iter, n)
            }

            fn binding_6<'a, T, const N: usize>(
                iter: ArrayWindows<'a, T, N>,
            ) -> (result: Option<<ArrayWindows<'a, T, N> as Iterator>::Item>)
                ensures
                    valid::<T, N>(iter@),
                    iter.remaining() == remaining::<T, N>(iter@),
                    item_values(iter.remaining()) == values::<T, N>(iter@),
                    if N <= iter@.len() {
                        result is Some && result.unwrap()@ == iter@.subrange(
                            iter@.len() - N,
                            iter@.len() as int,
                        )
                    } else {
                        result is None
                    },
            {
                <ArrayWindows<'a, T, N> as Iterator>::last(iter)
            }

            fn binding_7<'a, T, const N: usize>(
                iter: ArrayWindows<'a, T, N>,
            ) -> (result: usize)
                ensures
                    valid::<T, N>(iter@),
                    iter.remaining() == remaining::<T, N>(iter@),
                    item_values(iter.remaining()) == values::<T, N>(iter@),
                    result == values::<T, N>(iter@).len(),
            {
                <ArrayWindows<'a, T, N> as Iterator>::count(iter)
            }

            fn binding_8<'a, T, const N: usize>(
                iter: &ArrayWindows<'a, T, N>,
            ) -> (result: (usize, Option<usize>))
                ensures
                    valid::<T, N>(iter@),
                    iter.remaining() == remaining::<T, N>(iter@),
                    item_values(iter.remaining()) == values::<T, N>(iter@),
                    iter.obeys_prophetic_iter_laws(),
                    iter.will_return_none(),
                    iter.decrease() is Some,
                    result.0 == values::<T, N>(iter@).len(),
                    result.1 == Some(result.0),
            {
                <ArrayWindows<'a, T, N> as Iterator>::size_hint(iter)
            }

        }

        mod ascii {
            use core::slice::*;
            use vstd::prelude::*;
            use vstd::std_specs::iter::IteratorSpec;
            use vstd::std_specs::slice::ascii::*;

            fn binding_0(bytes: &[u8]) -> (result: EscapeAscii<'_>)
                ensures
                    ({
                        let (bytes, result): (Seq<u8>, EscapeAscii<'_>) = (bytes@, result);
                        ({
                            let (bytes, after, remaining, lawful, terminates, has_metric): (
                                Seq<u8>,
                                Parts,
                                Seq<u8>,
                                bool,
                                bool,
                                bool,
                            ) = (
                                bytes,
                                view(result),
                                IteratorSpec::remaining(&result),
                                IteratorSpec::obeys_prophetic_iter_laws(&result),
                                IteratorSpec::will_return_none(&result),
                                IteratorSpec::decrease(&result) is Some,
                            );
                            &&& ({
                                let (bytes, after): (Seq<u8>, Parts) = (bytes, after);
                                after == initial(bytes)
                            })
                            &&& ({
                                let (bytes, remaining, lawful, terminates, has_metric): (
                                    Seq<u8>,
                                    Seq<u8>,
                                    bool,
                                    bool,
                                    bool,
                                ) = (bytes, remaining, lawful, terminates, has_metric);
                                remaining == escaped(bytes) && lawful && terminates && has_metric
                            })
                        })
                    }),
            {
                <[u8]>::escape_ascii(bytes)
            }

            fn binding_1<'a>(
                iter: &mut EscapeAscii<'a>,
            ) -> (result: Option<u8>)
                ensures
                    ({
                        let (before, after, result): (Parts, Parts, Option<u8>) = (
                            view(*old(iter)),
                            view(*final(iter)),
                            result,
                        );
                        &&& after == front_parts(before)
                        &&& ({
                            let (before, after, result): (Seq<u8>, Seq<u8>, Option<u8>) = (
                                contents(before),
                                contents(after),
                                result,
                            );
                            if before.len() == 0 {
                                result == None && after == before
                            } else {
                                result == Some(before[0]) && after == before.drop_first()
                            }
                        })
                    }),
            {
                <EscapeAscii<'a> as Iterator>::next(iter)
            }

            fn binding_2<'a>(
                iter: &mut EscapeAscii<'a>,
            ) -> (result: Option<u8>)
                ensures
                    ({
                        let (before, after, result): (Parts, Parts, Option<u8>) = (
                            view(*old(iter)),
                            view(*final(iter)),
                            result,
                        );
                        &&& after == back_parts(before)
                        &&& ({
                            let (before, after, result): (Seq<u8>, Seq<u8>, Option<u8>) = (
                                contents(before),
                                contents(after),
                                result,
                            );
                            if before.len() == 0 {
                                result == None && after == before
                            } else {
                                result == Some(before.last()) && after == before.drop_last()
                            }
                        })
                    }),
            {
                <EscapeAscii<'a> as DoubleEndedIterator>::next_back(iter)
            }

            fn binding_3<'a>(
                iter: EscapeAscii<'a>,
            ) -> (result: Option<u8>)
                ensures
                    ({
                        let (before, remaining, result): (Parts, Seq<u8>, Option<u8>) = (
                            view(iter),
                            IteratorSpec::remaining(&iter),
                            result,
                        );
                        &&& remaining == contents(before)
                        &&& ({
                            let (before, result): (Parts, Option<u8>) = (before, result);
                            ({
                                let (before, result): (Seq<u8>, Option<u8>) = (contents(before), result);
                                result == if before.len() == 0 {
                                    None
                                } else {
                                    Some(before.last())
                                }
                            })
                        })
                        &&& ({
                            let (before, result): (Seq<u8>, Option<u8>) = (remaining, result);
                            result == if before.len() == 0 {
                                None
                            } else {
                                Some(before.last())
                            }
                        })
                    }),
            {
                <EscapeAscii<'a> as Iterator>::last(iter)
            }

            fn binding_4<'a>(
                iter: &EscapeAscii<'a>,
            ) -> (result: (usize, Option<usize>))
                ensures
                    ({
                        let (before, remaining, result): (Parts, Seq<u8>, (usize, Option<usize>)) = (
                            view(*iter),
                            IteratorSpec::remaining(iter),
                            result,
                        );
                        &&& remaining == contents(before)
                        &&& ({
                            let (before, result): (Parts, (usize, Option<usize>)) = (before, result);
                            result == hint_from_parts(before.0, before.1, before.2)
                        })
                        &&& ({
                            let (remaining, result): (Seq<u8>, (usize, Option<usize>)) = (remaining, result);
                            &&& result.0 <= remaining.len()
                            &&& match result.1 {
                                Some(upper) => result.0 == upper && upper == remaining.len(),
                                None => result.0 < remaining.len(),
                            }
                        })
                    }),
            {
                <EscapeAscii<'a> as Iterator>::size_hint(iter)
            }

            fn binding_5(bytes: &[u8]) -> (result: bool)
                ensures
                    result == is_ascii(bytes@),
            {
                <[u8]>::is_ascii(bytes)
            }

            fn binding_6<'a>(
                iter: &EscapeAscii<'a>,
            ) -> (result: EscapeAscii<'a>)
                ensures
                    IteratorSpec::remaining(&result) == IteratorSpec::remaining(iter),
                    IteratorSpec::obeys_prophetic_iter_laws(&result) == IteratorSpec::obeys_prophetic_iter_laws(
                        iter,
                    ),
                    IteratorSpec::will_return_none(&result) == IteratorSpec::will_return_none(iter),
                    IteratorSpec::decrease(&result) == IteratorSpec::decrease(iter),
                    view(result) == view(*iter),
            {
                <EscapeAscii<'a> as Clone>::clone(iter)
            }

        }

        mod chunk_by {
            use core::slice::*;
            use vstd::prelude::*;
            use vstd::std_specs::iter::IteratorSpec;
            use vstd::std_specs::slice::chunk_by::*;

            fn binding_0<'a, T, P: FnMut(&T, &T) -> bool>(
                slice: &'a [T],
                pred: P,
            ) -> (result: ChunkBy<'a, T, P>)
                ensures
                    ({
                        let (slice, predicate, result): (Seq<T>, P, Current<T, P>) = (
                            slice@,
                            pred,
                            result.state(),
                        );
                        result.slice == slice && result.predicate == predicate
                    }),
            {
                <[T]>::chunk_by(slice, pred)
            }

            fn binding_1<'a, T, P: FnMut(&T, &T) -> bool>(
                slice: &'a mut [T],
                pred: P,
            ) -> (result: ChunkByMut<'a, T, P>)
                ensures
                    ({
                        let (slice, predicate, result, owner_final, field_final): (
                            Seq<T>,
                            P,
                            Current<T, P>,
                            Seq<T>,
                            Seq<T>,
                        ) = (old(slice)@, pred, result.state(), final(slice)@, result.future_slice());
                        ({
                            let (slice, predicate, result): (Seq<T>, P, Current<T, P>) = (
                                slice,
                                predicate,
                                result,
                            );
                            result.slice == slice && result.predicate == predicate
                        }) && owner_final == field_final
                    }),
            {
                <[T]>::chunk_by_mut(slice, pred)
            }

            fn binding_2<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &ChunkBy<'a, T, P>) -> (result: (usize, Option<usize>))
                ensures
                    ({
                        let (state, result): (Current<T, P>, (usize, Option<usize>)) = (iter.state(), result);
                        result == if state.slice.len() == 0 {
                            (0usize, Some(0usize))
                        } else {
                            (1usize, Some(state.slice.len() as usize))
                        }
                    }),
            {
                <ChunkBy<
                'a,
                T,
                P,
            > as Iterator>::size_hint(iter)
            }

            fn binding_3<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &ChunkByMut<'a, T, P>) -> (result: (usize, Option<usize>))
                ensures
                    ({
                        let (state, result): (Current<T, P>, (usize, Option<usize>)) = (iter.state(), result);
                        result == if state.slice.len() == 0 {
                            (0usize, Some(0usize))
                        } else {
                            (1usize, Some(state.slice.len() as usize))
                        }
                    }),
            {
                <ChunkByMut<
                'a,
                T,
                P,
            > as Iterator>::size_hint(iter)
            }

            fn binding_4<'a, T: 'a, P: Clone>(
                iter: &ChunkBy<'a, T, P>,
            ) -> (result: ChunkBy<'a, T, P>)
                ensures
                    clone_post(iter.state(), result.state()),
            {
                <ChunkBy<'a, T, P> as Clone>::clone(iter)
            }

            fn binding_5<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &mut ChunkBy<'a, T, P>) -> (result: Option<
                <ChunkBy<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>|
                        consumption_post(
                            old(iter).state(),
                            false,
                            final(iter).state(),
                            option_values(result),
                            scan,
                        ),
            {
                <ChunkBy<
                'a,
                T,
                P,
            > as Iterator>::next(iter)
            }

            fn binding_6<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &mut ChunkBy<'a, T, P>) -> (result: Option<
                <ChunkBy<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>|
                        consumption_post(
                            old(iter).state(),
                            true,
                            final(iter).state(),
                            option_values(result),
                            scan,
                        ),
            {
                <ChunkBy<
                'a,
                T,
                P,
            > as DoubleEndedIterator>::next_back(iter)
            }

            fn binding_7<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: ChunkBy<'a, T, P>) -> (result: Option<
                <ChunkBy<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>, remaining: Current<T, P>|
                        consumption_post(iter.state(), true, remaining, option_values(result), scan),
            {
                <ChunkBy<
                'a,
                T,
                P,
            > as Iterator>::last(iter)
            }

            fn binding_8<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &mut ChunkByMut<'a, T, P>) -> (result: Option<
                <ChunkByMut<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>|
                        mutable_post(
                            old(iter).state(),
                            false,
                            final(iter).state(),
                            mut_option_values(result),
                            scan,
                            old(iter).future_slice(),
                            final(iter).future_slice(),
                            mut_option_final(result),
                        ),
            {
                <ChunkByMut<
                'a,
                T,
                P,
            > as Iterator>::next(iter)
            }

            fn binding_9<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: &mut ChunkByMut<'a, T, P>) -> (result: Option<
                <ChunkByMut<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>|
                        mutable_post(
                            old(iter).state(),
                            true,
                            final(iter).state(),
                            mut_option_values(result),
                            scan,
                            old(iter).future_slice(),
                            final(iter).future_slice(),
                            mut_option_final(result),
                        ),
            {
                <ChunkByMut<
                'a,
                T,
                P,
            > as DoubleEndedIterator>::next_back(iter)
            }

            fn binding_10<'a, T: 'a, P: FnMut(&T, &T) -> bool>(iter: ChunkByMut<'a, T, P>) -> (result: Option<
                <ChunkByMut<'a, T, P> as Iterator>::Item,
            >)
                ensures
                    exists|scan: Scan<T, P>, remaining: Current<T, P>, remaining_final: Seq<T>|
                        mutable_post(
                            iter.state(),
                            true,
                            remaining,
                            mut_option_values(result),
                            scan,
                            iter.future_slice(),
                            remaining_final,
                            mut_option_final(result),
                        ),
            {
                <ChunkByMut<
                'a,
                T,
                P,
            > as Iterator>::last(iter)
            }

        }

        mod windows {
            use core::slice::*;
            use vstd::prelude::*;
            use vstd::std_specs::iter::IteratorSpec;
            use vstd::std_specs::slice::windows::*;

            fn binding_0<'a, T>(
                iter: &Windows<'a, T>,
            ) -> (result: Windows<'a, T>)
                ensures
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            iter@,
                            IteratorSpec::remaining(iter),
                            IteratorSpec::obeys_prophetic_iter_laws(iter),
                            IteratorSpec::will_return_none(iter),
                            IteratorSpec::decrease(iter),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            result@,
                            IteratorSpec::remaining(&result),
                            IteratorSpec::obeys_prophetic_iter_laws(&result),
                            IteratorSpec::will_return_none(&result),
                            IteratorSpec::decrease(&result),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (before, result): (State<T>, State<T>) = (iter@, result@);
                        result.v == before.v && result.width == before.width
                    }),
                    result.remaining() == iter.remaining(),
            {
                <Windows<'a, T> as Clone>::clone(iter)
            }

            fn binding_1<'a, T>(
                iter: &mut Windows<'a, T>,
            ) -> (result: Option<&'a [T]>)
                ensures
                    valid(old(iter)@),
                    valid(final(iter)@),
                    ({
                        let (before, after, result): (State<T>, State<T>, Option<Seq<T>>) = (
                            old(iter)@,
                            final(iter)@,
                            option_values(result),
                        );
                        after.width == before.width && if before.width > before.v.len() {
                            result == None && after.v == before.v
                        } else {
                            result == Some(before.v.subrange(0, before.width as int)) && after.v
                                == before.v.subrange(1, before.v.len() as int)
                        }
                    }),
            {
                <Windows<'a, T> as Iterator>::next(iter)
            }

            fn binding_2<'a, T>(
                iter: &mut Windows<'a, T>,
                n: usize,
            ) -> (result: Option<<Windows<'a, T> as Iterator>::Item>)
                ensures
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            old(iter)@,
                            IteratorSpec::remaining(old(iter)),
                            IteratorSpec::obeys_prophetic_iter_laws(old(iter)),
                            IteratorSpec::will_return_none(old(iter)),
                            IteratorSpec::decrease(old(iter)),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            final(iter)@,
                            IteratorSpec::remaining(final(iter)),
                            IteratorSpec::obeys_prophetic_iter_laws(final(iter)),
                            IteratorSpec::will_return_none(final(iter)),
                            IteratorSpec::decrease(final(iter)),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (before, n, after, result): (State<T>, usize, State<T>, Option<Seq<T>>) = (
                            old(iter)@,
                            n,
                            final(iter)@,
                            option_values(result),
                        );
                        after.width == before.width && if n < values(before).len() {
                            result == Some(before.v.subrange(n as int, n as int + before.width)) && after.v
                                == before.v.subrange(n as int + 1, before.v.len() as int)
                        } else {
                            result == None && after.v == Seq::<T>::empty()
                        }
                    }),
            {
                <Windows<'a, T> as Iterator>::nth(iter, n)
            }

            fn binding_3<'a, T>(
                iter: &mut Windows<'a, T>,
            ) -> (result: Option<<Windows<'a, T> as Iterator>::Item>)
                ensures
                    valid(old(iter)@),
                    valid(final(iter)@),
                    ({
                        let (before, after, result): (State<T>, State<T>, Option<Seq<T>>) = (
                            old(iter)@,
                            final(iter)@,
                            option_values(result),
                        );
                        ({
                            let (before, n, after, result): (State<T>, usize, State<T>, Option<Seq<T>>) = (
                                before,
                                0,
                                after,
                                result,
                            );
                            after.width == before.width && if n < values(before).len() {
                                let end = before.v.len() - n;
                                result == Some(before.v.subrange(end - before.width, end)) && after.v
                                    == before.v.subrange(0, end - 1)
                            } else {
                                result == None && after.v == Seq::<T>::empty()
                            }
                        })
                    }),
            {
                <Windows<'a, T> as DoubleEndedIterator>::next_back(iter)
            }

            fn binding_4<'a, T>(
                iter: &mut Windows<'a, T>,
                n: usize,
            ) -> (result: Option<<Windows<'a, T> as Iterator>::Item>)
                ensures
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            old(iter)@,
                            IteratorSpec::remaining(old(iter)),
                            IteratorSpec::obeys_prophetic_iter_laws(old(iter)),
                            IteratorSpec::will_return_none(old(iter)),
                            IteratorSpec::decrease(old(iter)),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (state, items, obeys, terminates, metric): (
                            State<T>,
                            Seq<&'a [T]>,
                            bool,
                            bool,
                            Option<nat>,
                        ) = (
                            final(iter)@,
                            IteratorSpec::remaining(final(iter)),
                            IteratorSpec::obeys_prophetic_iter_laws(final(iter)),
                            IteratorSpec::will_return_none(final(iter)),
                            IteratorSpec::decrease(final(iter)),
                        );
                        &&& valid(state)
                        &&& items == remaining(state)
                        &&& obeys
                        &&& terminates
                        &&& metric is Some
                    }),
                    ({
                        let (before, n, after, result): (State<T>, usize, State<T>, Option<Seq<T>>) = (
                            old(iter)@,
                            n,
                            final(iter)@,
                            option_values(result),
                        );
                        after.width == before.width && if n < values(before).len() {
                            let end = before.v.len() - n;
                            result == Some(before.v.subrange(end - before.width, end)) && after.v
                                == before.v.subrange(0, end - 1)
                        } else {
                            result == None && after.v == Seq::<T>::empty()
                        }
                    }),
            {
                <Windows<'a, T> as DoubleEndedIterator>::nth_back(iter, n)
            }

            fn binding_5<'a, T>(
                iter: Windows<'a, T>,
            ) -> (result: usize)
                ensures
                    ({
                        let (state, items): (State<T>, Seq<&'a [T]>) = (iter@, IteratorSpec::remaining(&iter));
                        valid(state) && items == remaining(state)
                    }),
                    ({
                        let (before, result): (State<T>, usize) = (iter@, result);
                        result == values(before).len()
                    }),
            {
                <Windows<'a, T> as Iterator>::count(iter)
            }

            fn binding_6<'a, T>(
                iter: Windows<'a, T>,
            ) -> (result: Option<<Windows<'a, T> as Iterator>::Item>)
                ensures
                    ({
                        let (state, items): (State<T>, Seq<&'a [T]>) = (iter@, IteratorSpec::remaining(&iter));
                        valid(state) && items == remaining(state)
                    }),
                    ({
                        let (before, result): (State<T>, Option<Seq<T>>) = (iter@, option_values(result));
                        if before.width > before.v.len() {
                            result == None
                        } else {
                            result == Some(
                                before.v.subrange(before.v.len() - before.width, before.v.len() as int),
                            )
                        }
                    }),
            {
                <Windows<'a, T> as Iterator>::last(iter)
            }

            fn binding_7<'a, T>(
                iter: &Windows<'a, T>,
            ) -> (result: (usize, Option<usize>))
                ensures
                    ({
                        let (state, items): (State<T>, Seq<&'a [T]>) = (iter@, IteratorSpec::remaining(iter));
                        valid(state) && items == remaining(state)
                    }),
                    ({
                        let (before, result): (State<T>, (usize, Option<usize>)) = (iter@, result);
                        result.0 == values(before).len() && result.1 == Some(result.0)
                    }),
            {
                <Windows<'a, T> as Iterator>::size_hint(iter)
            }

            fn binding_8<'a, T>(slice: &'a [T], size: usize) -> (result: Windows<
                'a,
                T,
            >)
                ensures
                    size > 0,
                    result@.v == slice@,
                    result@.width == size,
                    valid(result@),
                    result.remaining() == remaining(result@),
                    result.obeys_prophetic_iter_laws(),
                    result.will_return_none(),
                    result.decrease() is Some,
            {
                <[T]>::windows(slice, size)
            }

        }

    } => Ok(())
}
