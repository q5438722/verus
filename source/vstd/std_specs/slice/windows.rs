use crate::prelude::*;
use crate::std_specs::iter::IteratorSpec;
use core::slice::Windows;

verus! {

pub ghost struct State<T> {
    pub v: Seq<T>,
    pub width: usize,
}

pub open spec fn valid<T>(s: State<T>) -> bool {
    s.width > 0 && s.v.len() <= usize::MAX
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

pub open spec fn values<T>(s: State<T>) -> Seq<Seq<T>> {
    window_values(s.v, s.width)
}

pub open spec fn slice_contents<T>(slice: &[T], contents: Seq<T>) -> bool {
    slice@ == contents
}

pub open spec fn content_ref<'a, T>(contents: Seq<T>) -> &'a [T] {
    choose|slice: &'a [T]| #[trigger] slice_contents(slice, contents)
}

pub open spec fn references<'a, T>(contents: Seq<Seq<T>>) -> Seq<&'a [T]> {
    Seq::new(contents.len(), |i: int| content_ref(contents[i]))
}

pub open spec fn remaining<'a, T>(s: State<T>) -> Seq<&'a [T]> {
    references(values(s))
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExWindows<'a, T: 'a>(Windows<'a, T>);

pub trait WindowsView<T> {
    spec fn view(&self) -> State<T>;
}

impl<'a, T> WindowsView<T> for Windows<'a, T> {
    uninterp spec fn view(&self) -> State<T>;
}

pub assume_specification<'a, T>[ <[T]>::windows ](slice: &'a [T], size: usize) -> (result: Windows<
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
;

pub open spec fn option_values<T>(item: Option<&[T]>) -> Option<Seq<T>> {
    match item {
        None => None,
        Some(slice) => Some(slice@),
    }
}

pub assume_specification<'a, T>[ <Windows<'a, T> as Clone>::clone ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as Iterator>::next ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as Iterator>::nth ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as DoubleEndedIterator>::next_back ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as DoubleEndedIterator>::nth_back ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as Iterator>::count ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as Iterator>::last ](
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
;

pub assume_specification<'a, T>[ <Windows<'a, T> as Iterator>::size_hint ](
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
;

} // verus!
