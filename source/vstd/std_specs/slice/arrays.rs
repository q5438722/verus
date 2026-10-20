pub mod array_slices {
    use crate::prelude::*;

    verus! {

pub open spec fn row_views<T, const N: usize>(rows: Seq<[T; N]>) -> Seq<Seq<T>> {
    rows.map_values(|row: [T; N]| row@)
}

pub open spec fn reshape<T>(values: Seq<T>, count: nat, width: nat) -> Seq<Seq<T>> {
    Seq::new(count, |i: int| values.subrange(i * width, (i + 1) * width))
}

pub assume_specification<T, const N: usize>[ <[T]>::as_array ](slice: &[T]) -> (result: Option<
    &[T; N],
>)
    ensures
        match result {
            Some(array) => slice@.len() == N && array@ == slice@,
            None => slice@.len() != N,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::first_chunk ](slice: &[T]) -> (result: Option<
    &[T; N],
>)
    ensures
        match result {
            Some(array) => N <= slice@.len() && array@ == slice@.subrange(0, N as int),
            None => slice@.len() < N,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::last_chunk ](slice: &[T]) -> (result: Option<
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
;

pub assume_specification<T, const N: usize>[ <[T]>::split_first_chunk ](slice: &[T]) -> (result:
    Option<(&[T; N], &[T])>)
    ensures
        match result {
            Some((array, tail)) => N <= slice@.len() && array@ == slice@.subrange(0, N as int)
                && tail@ == slice@.subrange(N as int, slice@.len() as int),
            None => slice@.len() < N,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::split_last_chunk ](slice: &[T]) -> (result:
    Option<(&[T], &[T; N])>)
    ensures
        match result {
            Some((init, array)) => N <= slice@.len() && init@ == slice@.subrange(
                0,
                slice@.len() - N,
            ) && array@ == slice@.subrange(slice@.len() - N, slice@.len() as int),
            None => slice@.len() < N,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::as_mut_array ](slice: &mut [T]) -> (result:
    Option<&mut [T; N]>)
    ensures
        match result {
            Some(array) => old(slice)@.len() == N && array@ == old(slice)@ && final(array)@.len()
                == N && final(slice)@ == final(array)@,
            None => old(slice)@.len() != N && final(slice)@ == old(slice)@,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::first_chunk_mut ](slice: &mut [T]) -> (result:
    Option<&mut [T; N]>)
    ensures
        match result {
            Some(array) => N <= old(slice)@.len() && array@ == old(slice)@.subrange(0, N as int)
                && final(array)@.len() == N && final(slice)@ == final(array)@ + old(
                slice,
            )@.subrange(N as int, old(slice)@.len() as int),
            None => old(slice)@.len() < N && final(slice)@ == old(slice)@,
        },
;

pub assume_specification<T, const N: usize>[ <[T]>::last_chunk_mut ](slice: &mut [T]) -> (result:
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
;

pub assume_specification<T, const N: usize>[ <[T]>::split_first_chunk_mut ](
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
;

pub assume_specification<T, const N: usize>[ <[T]>::split_last_chunk_mut ](
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
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_unchecked ](slice: &[T]) -> (result:
    &[[T; N]])
    requires
        N > 0,
        slice@.len() % (N as nat) == 0,
    ensures
        row_views(result@) == reshape(slice@, slice@.len() / (N as nat), N as nat),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks ](slice: &[T]) -> (result: (
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
;

pub assume_specification<T, const N: usize>[ <[T]>::as_rchunks ](slice: &[T]) -> (result: (
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
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_unchecked_mut ](
    slice: &mut [T],
) -> (result: &mut [[T; N]])
    requires
        N > 0,
        old(slice)@.len() % (N as nat) == 0,
    ensures
        row_views(result@) == reshape(old(slice)@, old(slice)@.len() / (N as nat), N as nat),
        result@.len() == old(slice)@.len() / (N as nat),
        final(result)@.len() == old(slice)@.len() / (N as nat),
        final(slice)@.len() == old(slice)@.len(),
        final(slice)@ == row_views(final(result)@).flatten(),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_mut ](slice: &mut [T]) -> (result: (
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
;

pub assume_specification<T, const N: usize>[ <[T]>::as_rchunks_mut ](slice: &mut [T]) -> (result: (
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
;

pub assume_specification<T, const N: usize>[ <[[T; N]]>::as_flattened ](
    slice: &[[T; N]],
) -> (result: &[T])
    ensures
        result@ == row_views(slice@).flatten(),
;

pub assume_specification<T, const N: usize>[ <[[T; N]]>::as_flattened_mut ](
    slice: &mut [[T; N]],
) -> (result: &mut [T])
    ensures
        result@ == row_views(old(slice)@).flatten(),
        result@.len() == old(slice)@.len() * N,
        final(result)@.len() == old(slice)@.len() * N,
        final(slice)@.len() == old(slice)@.len(),
        row_views(final(slice)@) == reshape(final(result)@, old(slice)@.len(), N as nat),
;

} // verus!
}

pub mod array_windows {
    use crate::prelude::*;
    use crate::std_specs::iter::IteratorSpec;
    use core::slice::ArrayWindows;

    verus! {

pub open spec fn array_contents<T, const N: usize>(array: &[T; N], contents: Seq<T>) -> bool {
    array@ == contents
}

pub open spec fn content_ref<'a, T, const N: usize>(contents: Seq<T>) -> &'a [T; N] {
    choose|array: &'a [T; N]| #[trigger] array_contents(array, contents)
}

pub open spec fn window_values<T>(values: Seq<T>, width: usize) -> Seq<Seq<T>>
    recommends
        width > 0,
{
    Seq::new(
        if width <= values.len() {
            (values.len() - width + 1) as nat
        } else {
            0
        },
        |i: int| values.subrange(i, i + width),
    )
}

pub type State<T> = Seq<T>;

pub open spec fn valid<T, const N: usize>(state: State<T>) -> bool {
    N > 0 && state.len() <= usize::MAX
}

pub open spec fn values<T, const N: usize>(state: State<T>) -> Seq<Seq<T>> {
    if N == 0 {
        Seq::empty()
    } else {
        window_values(state, N)
    }
}

pub open spec fn item_values<'a, T, const N: usize>(items: Seq<&'a [T; N]>) -> Seq<Seq<T>> {
    Seq::new(items.len(), |i: int| items[i]@)
}

pub open spec fn references<'a, T, const N: usize>(contents: Seq<Seq<T>>) -> Seq<&'a [T; N]> {
    Seq::new(contents.len(), |i: int| content_ref::<'a, T, N>(contents[i]))
}

pub open spec fn remaining<'a, T, const N: usize>(state: State<T>) -> Seq<&'a [T; N]> {
    references::<'a, T, N>(values::<T, N>(state))
}

pub open spec fn skip_front<T>(before: State<T>, n: usize) -> State<T> {
    before.subrange(
        if n <= before.len() {
            n as int
        } else {
            before.len() as int
        },
        before.len() as int,
    )
}

pub open spec fn skip_back<T>(before: State<T>, n: usize) -> State<T> {
    before.subrange(
        0,
        if n <= before.len() {
            before.len() - n
        } else {
            0
        },
    )
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExArrayWindows<'a, T: 'a, const N: usize>(ArrayWindows<'a, T, N>);

pub trait ArrayWindowsView<T> {
    spec fn view(&self) -> State<T>;
}

impl<'a, T, const N: usize> ArrayWindowsView<T> for ArrayWindows<'a, T, N> {
    uninterp spec fn view(&self) -> State<T>;
}

pub assume_specification<'a, T, const N: usize>[ <[T]>::array_windows ](slice: &'a [T]) -> (result:
    ArrayWindows<'a, T, N>)
    ensures
        N > 0,
        result@ == slice@,
        result.remaining() == remaining::<T, N>(result@),
        item_values(result.remaining()) == values::<T, N>(result@),
        result.obeys_prophetic_iter_laws(),
        result.will_return_none(),
        result.decrease() is Some,
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Iterator>::next ](
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<
    'a,
    T,
    N,
> as DoubleEndedIterator>::next_back ](iter: &mut ArrayWindows<'a, T, N>) -> (result: Option<
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Iterator>::nth ](
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<
    'a,
    T,
    N,
> as DoubleEndedIterator>::nth_back ](iter: &mut ArrayWindows<'a, T, N>, n: usize) -> (result:
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Iterator>::last ](
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Iterator>::count ](
    iter: ArrayWindows<'a, T, N>,
) -> (result: usize)
    ensures
        valid::<T, N>(iter@),
        iter.remaining() == remaining::<T, N>(iter@),
        item_values(iter.remaining()) == values::<T, N>(iter@),
        result == values::<T, N>(iter@).len(),
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Iterator>::size_hint ](
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
;

pub assume_specification<'a, T, const N: usize>[ <ArrayWindows<'a, T, N> as Clone>::clone ](
    iter: &ArrayWindows<'a, T, N>,
) -> (result: ArrayWindows<'a, T, N>)
    ensures
        result == *iter,
        result.remaining() == iter.remaining(),
        result.obeys_prophetic_iter_laws() == iter.obeys_prophetic_iter_laws(),
        result.will_return_none() == iter.will_return_none(),
        result.decrease() == iter.decrease(),
;

} // verus!
}
