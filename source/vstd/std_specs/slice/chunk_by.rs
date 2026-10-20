use crate::prelude::*;
use core::slice::{ChunkBy, ChunkByMut};

verus! {

#[verifier::prophetic]
pub open spec fn ordered_states<F>(initial: F, calls: Seq<&mut F>) -> bool {
    &&& calls.len() > 0 ==> *calls[0] == initial
    &&& forall|i: int| 0 <= i < calls.len() - 1 ==> *final(#[trigger] calls[i]) == *calls[i + 1]
}

pub ghost struct Current<T, P> {
    pub slice: Seq<T>,
    pub predicate: P,
}

pub open spec fn clone_post<T, P: Clone>(before: Current<T, P>, result: Current<T, P>) -> bool {
    result.slice == before.slice && call_ensures(P::clone, (&before.predicate,), result.predicate)
}

pub open spec fn option_values<T>(item: Option<&[T]>) -> Option<Seq<T>> {
    match item {
        None => None,
        Some(slice) => Some(slice@),
    }
}

pub open spec fn mut_option_values<T>(item: Option<&mut [T]>) -> Option<Seq<T>> {
    match item {
        None => None,
        Some(slice) => Some(slice@),
    }
}

#[verifier::prophetic]
pub open spec fn mut_option_final<T>(item: Option<&mut [T]>) -> Option<Seq<T>> {
    match item {
        None => None,
        Some(slice) => Some(final(slice)@),
    }
}

pub ghost struct Scan<'a, T, P> {
    pub calls: Seq<&'a mut P>,
    pub args: Seq<(&'a T, &'a T)>,
    pub outputs: Seq<bool>,
}

pub open spec fn pair_index(n: nat, back: bool, call: int) -> int {
    if back {
        n - 2 - call
    } else {
        call
    }
}

#[verifier::prophetic]
pub open spec fn binary_trace<'a, T, P: FnMut(&T, &T) -> bool>(
    initial: P,
    scan: Scan<'a, T, P>,
    final_predicate: P,
) -> bool {
    &&& scan.calls.len() == scan.args.len() == scan.outputs.len()
    &&& ordered_states(initial, scan.calls)
    &&& if scan.calls.len() == 0 {
        final_predicate == initial
    } else {
        final_predicate == *final(scan.calls.last())
    }
    &&& forall|i: int|
        0 <= i < scan.calls.len() ==> {
            &&& call_requires(#[trigger] scan.calls[i], scan.args[i])
            &&& call_ensures(scan.calls[i], scan.args[i], scan.outputs[i])
        }
}

#[verifier::prophetic]
pub open spec fn scan_post<'a, T, P: FnMut(&T, &T) -> bool>(
    before: Current<T, P>,
    back: bool,
    scan: Scan<'a, T, P>,
    final_predicate: P,
) -> bool {
    let n = before.slice.len();
    let count = scan.calls.len();
    &&& binary_trace(before.predicate, scan, final_predicate)
    &&& count <= if n == 0 {
        0
    } else {
        n - 1
    }
    &&& if count == 0 {
        n <= 1
    } else {
        !scan.outputs.last() || count == n - 1
    }
    &&& forall|i: int|
        0 <= i < count ==> {
            let k = pair_index(n, back, i);
            &&& *#[trigger] scan.args[i].0 == before.slice[k]
            &&& *scan.args[i].1 == before.slice[k + 1]
            &&& i + 1 < count ==> scan.outputs[i]
        }
}

pub open spec fn selected_len<'a, T, P>(before: Current<T, P>, scan: Scan<'a, T, P>) -> nat {
    if scan.outputs.len() == 0 || scan.outputs.last() {
        before.slice.len()
    } else {
        scan.outputs.len()
    }
}

pub open spec fn split_post<T, P>(
    before: Current<T, P>,
    back: bool,
    width: nat,
    after: Current<T, P>,
    result: Option<Seq<T>>,
) -> bool {
    if before.slice.len() == 0 {
        width == 0 && result is None && after.slice == before.slice
    } else {
        let cut = if back {
            before.slice.len() - width
        } else {
            width as int
        };
        &&& 1 <= width <= before.slice.len()
        &&& result == Some(
            if back {
                before.slice.subrange(cut, before.slice.len() as int)
            } else {
                before.slice.subrange(0, cut)
            },
        )
        &&& after.slice == if back {
            before.slice.subrange(0, cut)
        } else {
            before.slice.subrange(cut, before.slice.len() as int)
        }
    }
}

#[verifier::prophetic]
pub open spec fn consumption_post<'a, T, P: FnMut(&T, &T) -> bool>(
    before: Current<T, P>,
    back: bool,
    after: Current<T, P>,
    result: Option<Seq<T>>,
    scan: Scan<'a, T, P>,
) -> bool {
    scan_post(before, back, scan, after.predicate) && split_post(
        before,
        back,
        selected_len(before, scan),
        after,
        result,
    )
}

pub open spec fn writeback_post<T>(
    back: bool,
    result: Option<Seq<T>>,
    remaining: Seq<T>,
    before_final: Seq<T>,
    remaining_final: Seq<T>,
    result_final: Option<Seq<T>>,
) -> bool {
    &&& remaining_final.len() == remaining.len()
    &&& match (result, result_final) {
        (None, None) => before_final == remaining_final,
        (Some(initial), Some(written)) => {
            &&& written.len() == initial.len()
            &&& before_final == if back {
                remaining_final + written
            } else {
                written + remaining_final
            }
        },
        _ => false,
    }
}

#[verifier::prophetic]
pub open spec fn mutable_post<'a, T, P: FnMut(&T, &T) -> bool>(
    before: Current<T, P>,
    back: bool,
    after: Current<T, P>,
    result: Option<Seq<T>>,
    scan: Scan<'a, T, P>,
    before_final: Seq<T>,
    remaining_final: Seq<T>,
    result_final: Option<Seq<T>>,
) -> bool {
    consumption_post(before, back, after, result, scan) && writeback_post(
        back,
        result,
        after.slice,
        before_final,
        remaining_final,
        result_final,
    )
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkBy<'a, T: 'a, P>(ChunkBy<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkByMut<'a, T: 'a, P>(ChunkByMut<'a, T, P>);

pub trait ChunkByState<T, P> {
    spec fn state(&self) -> Current<T, P>;
}

impl<'a, T, P> ChunkByState<T, P> for ChunkBy<'a, T, P> {
    uninterp spec fn state(&self) -> Current<T, P>;
}

impl<'a, T, P> ChunkByState<T, P> for ChunkByMut<'a, T, P> {
    uninterp spec fn state(&self) -> Current<T, P>;
}

pub trait ChunkByFuture<T> {
    #[verifier::prophetic]
    spec fn future_slice(&self) -> Seq<T>;
}

impl<'a, T, P> ChunkByFuture<T> for ChunkByMut<'a, T, P> {
    #[verifier::prophetic]
    uninterp spec fn future_slice(&self) -> Seq<T>;
}

pub assume_specification<'a, T: 'a, P: Clone>[ <ChunkBy<'a, T, P> as Clone>::clone ](
    iter: &ChunkBy<'a, T, P>,
) -> (result: ChunkBy<'a, T, P>)
    ensures
        clone_post(iter.state(), result.state()),
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkBy<
    'a,
    T,
    P,
> as Iterator>::next ](iter: &mut ChunkBy<'a, T, P>) -> (result: Option<
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
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkBy<
    'a,
    T,
    P,
> as DoubleEndedIterator>::next_back ](iter: &mut ChunkBy<'a, T, P>) -> (result: Option<
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
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkBy<
    'a,
    T,
    P,
> as Iterator>::last ](iter: ChunkBy<'a, T, P>) -> (result: Option<
    <ChunkBy<'a, T, P> as Iterator>::Item,
>)
    ensures
        exists|scan: Scan<T, P>, remaining: Current<T, P>|
            consumption_post(iter.state(), true, remaining, option_values(result), scan),
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkByMut<
    'a,
    T,
    P,
> as Iterator>::next ](iter: &mut ChunkByMut<'a, T, P>) -> (result: Option<
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
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkByMut<
    'a,
    T,
    P,
> as DoubleEndedIterator>::next_back ](iter: &mut ChunkByMut<'a, T, P>) -> (result: Option<
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
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkByMut<
    'a,
    T,
    P,
> as Iterator>::last ](iter: ChunkByMut<'a, T, P>) -> (result: Option<
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
;

pub assume_specification<'a, T, P: FnMut(&T, &T) -> bool>[ <[T]>::chunk_by ](
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
;

pub assume_specification<'a, T, P: FnMut(&T, &T) -> bool>[ <[T]>::chunk_by_mut ](
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
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkBy<
    'a,
    T,
    P,
> as Iterator>::size_hint ](iter: &ChunkBy<'a, T, P>) -> (result: (usize, Option<usize>))
    ensures
        ({
            let (state, result): (Current<T, P>, (usize, Option<usize>)) = (iter.state(), result);
            result == if state.slice.len() == 0 {
                (0usize, Some(0usize))
            } else {
                (1usize, Some(state.slice.len() as usize))
            }
        }),
;

pub assume_specification<'a, T: 'a, P: FnMut(&T, &T) -> bool>[ <ChunkByMut<
    'a,
    T,
    P,
> as Iterator>::size_hint ](iter: &ChunkByMut<'a, T, P>) -> (result: (usize, Option<usize>))
    ensures
        ({
            let (state, result): (Current<T, P>, (usize, Option<usize>)) = (iter.state(), result);
            result == if state.slice.len() == 0 {
                (0usize, Some(0usize))
            } else {
                (1usize, Some(state.slice.len() as usize))
            }
        }),
;

} // verus!
