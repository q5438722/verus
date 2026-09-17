// Additional Rust standard-library Slice specifications generated from the
// independently audited zero-UF corpus. Existing stronger vstd specifications
// remain in `slice.rs`; this module contains only previously uncovered targets.
use super::super::prelude::*;
use super::super::slice::SliceIndexSpec;
use super::cmp::PartialEqSpec;

use verus as verus_;

verus_! {

#[verifier::external_type_specification]
pub struct ExOneSidedRangeBound(core::ops::OneSidedRangeBound);

#[verifier::external_trait_specification]
pub trait ExOneSidedRange<T>: core::ops::RangeBounds<T> {
    type ExternalTraitSpecificationFor: core::ops::OneSidedRange<T>;

    fn bound(self) -> (ret: (core::ops::OneSidedRangeBound, T));
}

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExCoreRangeFrom<Idx>(core::range::RangeFrom<Idx>);

#[verifier::external_type_specification]
#[verifier::reject_recursive_types(Idx)]
pub struct ExCoreRangeToInclusive<Idx>(core::range::RangeToInclusive<Idx>);

pub assume_specification<T>[
    <core::ops::RangeFrom<T> as core::ops::OneSidedRange<T>>::bound
](range: core::ops::RangeFrom<T>) -> (ret: (core::ops::OneSidedRangeBound, T))
    where core::ops::RangeFrom<T>: core::ops::RangeBounds<T>
    ensures
        ret == (core::ops::OneSidedRangeBound::StartInclusive, range.start),
;

pub assume_specification<T>[
    <core::ops::RangeTo<T> as core::ops::OneSidedRange<T>>::bound
](range: core::ops::RangeTo<T>) -> (ret: (core::ops::OneSidedRangeBound, T))
    where core::ops::RangeTo<T>: core::ops::RangeBounds<T>
    ensures
        ret == (core::ops::OneSidedRangeBound::End, range.end),
;

pub assume_specification<T>[
    <core::ops::RangeToInclusive<T> as core::ops::OneSidedRange<T>>::bound
](range: core::ops::RangeToInclusive<T>) -> (ret: (core::ops::OneSidedRangeBound, T))
    where core::ops::RangeToInclusive<T>: core::ops::RangeBounds<T>
    ensures
        ret == (core::ops::OneSidedRangeBound::EndInclusive, range.end),
;

pub assume_specification<T>[
    <core::range::RangeFrom<T> as core::ops::OneSidedRange<T>>::bound
](range: core::range::RangeFrom<T>) -> (ret: (core::ops::OneSidedRangeBound, T))
    where core::range::RangeFrom<T>: core::ops::RangeBounds<T>
    ensures
        ret == (core::ops::OneSidedRangeBound::StartInclusive, range.start),
;

pub assume_specification<T>[
    <core::range::RangeToInclusive<T> as core::ops::OneSidedRange<T>>::bound
](range: core::range::RangeToInclusive<T>) -> (ret: (core::ops::OneSidedRangeBound, T))
    where core::range::RangeToInclusive<T>: core::ops::RangeBounds<T>
    ensures
        ret == (core::ops::OneSidedRangeBound::EndInclusive, range.last),
;

#[verifier::external_trait_specification]
pub trait ExSlicePattern {
    type ExternalTraitSpecificationFor: core::slice::SlicePattern;

    type Item;

    fn as_slice(&self) -> (ret: &[Self::Item]);
}

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunks<'a, T: 'a>(core::slice::Chunks<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksExact<'a, T: 'a>(core::slice::ChunksExact<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksMut<'a, T: 'a>(core::slice::ChunksMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksExactMut<'a, T: 'a>(core::slice::ChunksExactMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunks<'a, T: 'a>(core::slice::RChunks<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksExact<'a, T: 'a>(core::slice::RChunksExact<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksMut<'a, T: 'a>(core::slice::RChunksMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksExactMut<'a, T: 'a>(core::slice::RChunksExactMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExWindows<'a, T: 'a>(core::slice::Windows<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExArrayWindows<'a, T: 'a, const N: usize>(core::slice::ArrayWindows<'a, T, N>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkBy<'a, T: 'a, P>(core::slice::ChunkBy<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkByMut<'a, T: 'a, P>(core::slice::ChunkByMut<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExUtf8Chunks<'a>(core::str::Utf8Chunks<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEscapeAscii<'a>(core::slice::EscapeAscii<'a>);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExGetDisjointMutError(core::slice::GetDisjointMutError);

#[verifier::reject_recursive_types(Idx)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExCoreRange<Idx>(core::range::Range<Idx>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplit<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::Split<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitMut<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::SplitMut<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitInclusive<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::SplitInclusive<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitInclusiveMut<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::SplitInclusiveMut<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitN<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::SplitN<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitNMut<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::SplitNMut<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplit<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::RSplit<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitMut<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::RSplitMut<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitN<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::RSplitN<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitNMut<'a, T: 'a, P: core::ops::FnMut(&T) -> bool>(
    core::slice::RSplitNMut<'a, T, P>,
);

pub assume_specification<T: core::cmp::Ord>[ <[T]>::binary_search ](
    slice: &[T],
    x: &T,
) -> (result: core::result::Result<usize, usize>)

    ensures
        result.is_ok() ==> result.unwrap() < slice@.len(),
        result.is_err() ==> result.unwrap_err() <= slice@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&'a T) -> core::cmp::Ordering>[
    <[T]>::binary_search_by::<F>
](
    slice: &'a [T],
    f: F,
) -> (result: core::result::Result<usize, usize>)

    ensures
        result.is_ok() ==> result.unwrap() < slice@.len(),
        result.is_err() ==> result.unwrap_err() <= slice@.len(),
;

pub assume_specification<'a, T, B: core::cmp::Ord, F: core::ops::FnMut(&'a T) -> B>[
    <[T]>::binary_search_by_key::<B, F>
](
    slice: &'a [T],
    key: &B,
    f: F,
) -> (result: core::result::Result<usize, usize>)

    ensures
        result.is_ok() ==> result.unwrap() < slice@.len(),
        result.is_err() ==> result.unwrap_err() <= slice@.len(),
;

pub assume_specification<T: core::cmp::PartialEq>[ <[T]>::contains ](
    slice: &[T],
    x: &T,
) -> (b: bool)

    ensures
        T::obeys_eq_spec() ==> (
            b <==> exists|i: int| {
                &&& 0 <= i < slice@.len()
                &&& slice@[i].eq_spec(x)
            }
        ),
;

pub assume_specification<T, P: core::ops::FnMut(&T) -> bool>[ <[T]>::partition_point::<P> ](
    slice: &[T],
    pred: P,
) -> (index: usize)

    ensures
        index <= slice@.len(),
        slice@.len() == 0 ==> index == 0,
;

pub assume_specification<T>[ <[T]>::split_at_unchecked ](
    slice: &[T],
    mid: usize,
) -> (ret: (&[T], &[T]))
    requires
        mid <= slice@.len(),
    ensures
        ret.0@ == slice@.subrange(0, mid as int),
        ret.1@ == slice@.subrange(mid as int, slice@.len() as int),
;

pub assume_specification<T>[ <[T]>::split_at_mut_checked ](
    slice: &mut [T],
    mid: usize,
) -> (ret: Option<(&mut [T], &mut [T])>)
    ensures
        mid <= old(slice)@.len() ==> ret.is_some()
            && ret.unwrap().0@ == old(slice)@.subrange(0, mid as int)
            && ret.unwrap().1@ == old(slice)@.subrange(mid as int, old(slice)@.len() as int)
            && final(slice)@ == final(ret.unwrap().0)@ + final(ret.unwrap().1)@,
        mid > old(slice)@.len() ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T>[ <[T]>::split_at_mut_unchecked ](
    slice: &mut [T],
    mid: usize,
) -> (ret: (&mut [T], &mut [T]))
    requires
        mid <= old(slice)@.len(),
    ensures
        ret.0@ == old(slice)@.subrange(0, mid as int),
        ret.1@ == old(slice)@.subrange(mid as int, old(slice)@.len() as int),
        final(slice)@ == final(ret.0)@ + final(ret.1)@,
;

pub assume_specification<T>[ <[T]>::split_last ](
    slice: &[T],
) -> (ret: Option<(&T, &[T])>)
    ensures
        slice@.len() == 0 ==> ret.is_none(),
        slice@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == slice@[(slice@.len() - 1) as int]
            && ret.unwrap().1@ == slice@.subrange(0, (slice@.len() - 1) as int),
;

pub assume_specification<T>[ <[T]>::split_last_mut ](
    slice: &mut [T],
) -> (ret: Option<(&mut T, &mut [T])>)
    ensures
        old(slice)@.len() == 0 ==> ret.is_none() && final(slice)@ == old(slice)@,
        old(slice)@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == old(slice)@[(old(slice)@.len() - 1) as int]
            && ret.unwrap().1@ == old(slice)@.subrange(0, (old(slice)@.len() - 1) as int)
            && final(slice)@ == final(ret.unwrap().1)@ + seq![*final(ret.unwrap().0)],
;

pub assume_specification<T, const N: usize>[ <[T]>::first_chunk::<N> ](
    slice: &[T],
) -> (ret: Option<&[T; N]>)
    ensures
        (N as int) <= slice@.len() ==> ret.is_some()
            && ret.unwrap()@ == slice@.subrange(0, N as int),
        (N as int) > slice@.len() ==> ret.is_none(),
;

pub assume_specification<T, const N: usize>[ <[T]>::last_chunk::<N> ](
    slice: &[T],
) -> (ret: Option<&[T; N]>)
    ensures
        (N as int) <= slice@.len() ==> ret.is_some()
            && ret.unwrap()@ == slice@.subrange((slice@.len() - N) as int, slice@.len() as int),
        (N as int) > slice@.len() ==> ret.is_none(),
;

pub assume_specification<T, const N: usize>[ <[T]>::first_chunk_mut::<N> ](
    slice: &mut [T],
) -> (ret: Option<&mut [T; N]>)
    ensures
        (N as int) <= old(slice)@.len() ==> ret.is_some()
            && ret.unwrap()@ == old(slice)@.subrange(0, N as int)
            && final(slice)@
                == final(ret.unwrap())@
                    + old(slice)@.subrange(N as int, old(slice)@.len() as int),
        (N as int) > old(slice)@.len() ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::last_chunk_mut::<N> ](
    slice: &mut [T],
) -> (ret: Option<&mut [T; N]>)
    ensures
        (N as int) <= old(slice)@.len() ==> ret.is_some()
            && ret.unwrap()@ == old(slice)@.subrange((old(slice)@.len() - N) as int, old(slice)@.len() as int)
            && final(slice)@
                == old(slice)@.subrange(0, (old(slice)@.len() - N) as int)
                    + final(ret.unwrap())@,
        (N as int) > old(slice)@.len() ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::split_first_chunk::<N> ](
    slice: &[T],
) -> (ret: Option<(&[T; N], &[T])>)
    ensures
        (N as int) <= slice@.len() ==> ret.is_some()
            && ret.unwrap().0@ == slice@.subrange(0, N as int)
            && ret.unwrap().1@ == slice@.subrange(N as int, slice@.len() as int),
        (N as int) > slice@.len() ==> ret.is_none(),
;

pub assume_specification<T, const N: usize>[ <[T]>::split_last_chunk::<N> ](
    slice: &[T],
) -> (ret: Option<(&[T], &[T; N])>)
    ensures
        (N as int) <= slice@.len() ==> ret.is_some()
            && ret.unwrap().0@ == slice@.subrange(0, (slice@.len() - N) as int)
            && ret.unwrap().1@ == slice@.subrange((slice@.len() - N) as int, slice@.len() as int),
        (N as int) > slice@.len() ==> ret.is_none(),
;

pub assume_specification<T, const N: usize>[ <[T]>::split_first_chunk_mut::<N> ](
    slice: &mut [T],
) -> (ret: Option<(&mut [T; N], &mut [T])>)
    ensures
        (N as int) <= old(slice)@.len() ==> ret.is_some()
            && ret.unwrap().0@ == old(slice)@.subrange(0, N as int)
            && ret.unwrap().1@ == old(slice)@.subrange(N as int, old(slice)@.len() as int)
            && final(slice)@
                == final(ret.unwrap().0)@ + final(ret.unwrap().1)@,
        (N as int) > old(slice)@.len() ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::split_last_chunk_mut::<N> ](
    slice: &mut [T],
) -> (ret: Option<(&mut [T], &mut [T; N])>)
    ensures
        (N as int) <= old(slice)@.len() ==> ret.is_some()
            && ret.unwrap().0@ == old(slice)@.subrange(0, (old(slice)@.len() - N) as int)
            && ret.unwrap().1@ == old(slice)@.subrange((old(slice)@.len() - N) as int, old(slice)@.len() as int)
            && final(slice)@
                == final(ret.unwrap().0)@ + final(ret.unwrap().1)@,
        (N as int) > old(slice)@.len() ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::as_array::<N> ](
    slice: &[T],
) -> (ret: Option<&[T; N]>)
    ensures
        slice@.len() == N ==> ret.is_some()
            && ret.unwrap()@ == slice@,
        slice@.len() != N ==> ret.is_none(),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_mut_array::<N> ](
    slice: &mut [T],
) -> (ret: Option<&mut [T; N]>)
    ensures
        old(slice)@.len() == N ==> ret.is_some()
            && ret.unwrap()@ == old(slice)@
            && final(slice)@ == final(ret.unwrap())@,
        old(slice)@.len() != N ==> ret.is_none() && final(slice)@ == old(slice)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks::<N> ](
    slice: &[T],
) -> (ret: (&[[T; N]], &[T]))
    requires
        N != 0,
    ensures
        ret.0@.len() == slice@.len() / (N as nat),
        forall|chunk: int| 0 <= chunk < ret.0@.len() ==> ret.0@[chunk]@
            == slice@.subrange(chunk * (N as int), (chunk + 1) * (N as int)),
        ret.1@ == slice@.subrange(
            (slice@.len() / (N as nat) * (N as nat)) as int, slice@.len() as int,
        ),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_rchunks::<N> ](
    slice: &[T],
) -> (ret: (&[T], &[[T; N]]))
    requires
        N != 0,
    ensures
        ret.1@.len() == slice@.len() / (N as nat),
        ret.0@ == slice@.subrange(0, (slice@.len() % (N as nat)) as int),
        forall|chunk: int| 0 <= chunk < ret.1@.len() ==> ret.1@[chunk]@
            == slice@.subrange(
                (slice@.len() % (N as nat)) as int + chunk * (N as int),
                (slice@.len() % (N as nat)) as int + (chunk + 1) * (N as int),
            ),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_unchecked::<N> ](
    slice: &[T],
) -> (ret: &[[T; N]])
    requires
        N != 0,
        slice@.len() % (N as nat) == 0,
    ensures
        ret@.len() == slice@.len() / (N as nat),
        forall|chunk: int| 0 <= chunk < ret@.len() ==> ret@[chunk]@
            == slice@.subrange(chunk * (N as int), (chunk + 1) * (N as int)),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_mut::<N> ](
    slice: &mut [T],
) -> (ret: (&mut [[T; N]], &mut [T]))
    requires
        N != 0,
    ensures
        ret.0@.len() == old(slice)@.len() / (N as nat),
        forall|chunk: int| 0 <= chunk < ret.0@.len() ==> ret.0@[chunk]@
            == old(slice)@.subrange(chunk * (N as int), (chunk + 1) * (N as int)),
        ret.1@ == old(slice)@.subrange(
            (old(slice)@.len() / (N as nat) * (N as nat)) as int,
            old(slice)@.len() as int,
        ),
        final(ret.0)@.len() == ret.0@.len(),
        final(ret.1)@.len() == ret.1@.len(),
        final(slice)@ == Seq::new(
            final(ret.0)@.len() * (N as nat),
            |i: int| final(ret.0)@[i / (N as int)]@[i % (N as int)],
        ) + final(ret.1)@,
;

pub assume_specification<T, const N: usize>[ <[T]>::as_rchunks_mut::<N> ](
    slice: &mut [T],
) -> (ret: (&mut [T], &mut [[T; N]]))
    requires
        N != 0,
    ensures
        ret.1@.len() == old(slice)@.len() / (N as nat),
        ret.0@ == old(slice)@.subrange(0, (old(slice)@.len() % (N as nat)) as int),
        forall|chunk: int| 0 <= chunk < ret.1@.len() ==> ret.1@[chunk]@
            == old(slice)@.subrange(
                (old(slice)@.len() % (N as nat)) as int + chunk * (N as int),
                (old(slice)@.len() % (N as nat)) as int + (chunk + 1) * (N as int),
            ),
        final(ret.1)@.len() == ret.1@.len(),
        final(ret.0)@.len() == ret.0@.len(),
        final(slice)@ == final(ret.0)@ + Seq::new(
            final(ret.1)@.len() * (N as nat),
            |i: int| final(ret.1)@[i / (N as int)]@[i % (N as int)],
        ),
;

pub assume_specification<T, const N: usize>[ <[T]>::as_chunks_unchecked_mut::<N> ](
    slice: &mut [T],
) -> (ret: &mut [[T; N]])
    requires
        N != 0,
        old(slice)@.len() % (N as nat) == 0,
    ensures
        ret@.len() == old(slice)@.len() / (N as nat),
        forall|chunk: int| 0 <= chunk < ret@.len() ==> ret@[chunk]@
            == old(slice)@.subrange(chunk * (N as int), (chunk + 1) * (N as int)),
        final(ret)@.len() == ret@.len(),
        final(slice)@ == Seq::new(
            final(ret)@.len() * (N as nat),
            |i: int| final(ret)@[i / (N as int)]@[i % (N as int)],
        ),
;

pub assume_specification<'a, T>[ <[T]>::chunks ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: core::slice::Chunks<'a, T>)

    requires
        chunk_size != 0,
;

pub assume_specification<'a, T>[ <[T]>::chunks_exact ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: core::slice::ChunksExact<'a, T>)

    requires
        chunk_size != 0,
;

pub assume_specification<'a, T>[ <[T]>::rchunks ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: core::slice::RChunks<'a, T>)

    requires
        chunk_size != 0,
;

pub assume_specification<'a, T>[ <[T]>::rchunks_exact ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: core::slice::RChunksExact<'a, T>)

    requires
        chunk_size != 0,
;

pub assume_specification<'a, T>[ <[T]>::windows ](
    slice: &'a [T],
    size: usize,
) -> (iter: core::slice::Windows<'a, T>)

    requires
        size != 0,
;

pub assume_specification<'a, T, const N: usize>[ <[T]>::array_windows::<N> ](
    slice: &'a [T],
) -> (iter: core::slice::ArrayWindows<'a, T, N>)

    requires
        N != 0,
;

pub assume_specification<'a, T>[ core::slice::ChunksExact::<'a, T>::remainder ](
    iter: &core::slice::ChunksExact<'a, T>,
) -> (ret: &'a [T])
;

pub assume_specification<'a, T>[ core::slice::ChunksExactMut::<'a, T>::into_remainder ](
    iter: core::slice::ChunksExactMut<'a, T>,
) -> (ret: &'a mut [T])

    ensures
        final(ret)@.len() == ret@.len(),
;

pub assume_specification<'a, T>[ core::slice::Iter::<'a, T>::as_slice ](
    iter: &core::slice::Iter<'a, T>,
) -> (ret: &'a [T])
;

pub assume_specification<'a, 'b, T>[ core::slice::IterMut::<'a, T>::as_slice ](
    iter: &'b core::slice::IterMut<'a, T>,
) -> (ret: &'b [T])
;

pub assume_specification<'a, T>[ core::slice::IterMut::<'a, T>::into_slice ](
    iter: core::slice::IterMut<'a, T>,
) -> (ret: &'a mut [T])

    ensures
        final(ret)@.len() == ret@.len(),
;

pub assume_specification<'a, T>[ core::slice::RChunksExact::<'a, T>::remainder ](
    iter: &core::slice::RChunksExact<'a, T>,
) -> (ret: &'a [T])
;

pub assume_specification<'a, T>[ core::slice::RChunksExactMut::<'a, T>::into_remainder ](
    iter: core::slice::RChunksExactMut<'a, T>,
) -> (ret: &'a mut [T])

    ensures
        final(ret)@.len() == ret@.len(),
;

pub assume_specification<'a, T>[ <[T]>::chunks_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: core::slice::ChunksMut<'a, T>)

    requires
        chunk_size != 0,
    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T>[ <[T]>::chunks_exact_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: core::slice::ChunksExactMut<'a, T>)

    requires
        chunk_size != 0,
    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T>[ <[T]>::rchunks_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: core::slice::RChunksMut<'a, T>)

    requires
        chunk_size != 0,
    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T>[ <[T]>::rchunks_exact_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: core::slice::RChunksExactMut<'a, T>)

    requires
        chunk_size != 0,
    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::split::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: core::slice::Split<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::split_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: core::slice::SplitMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::split_inclusive::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: core::slice::SplitInclusive<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[
    <[T]>::split_inclusive_mut::<F>
](
    slice: &'a mut [T],
    pred: F,
) -> (iter: core::slice::SplitInclusiveMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::splitn::<F> ](
    slice: &'a [T],
    n: usize,
    pred: F,
) -> (iter: core::slice::SplitN<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::splitn_mut::<F> ](
    slice: &'a mut [T],
    n: usize,
    pred: F,
) -> (iter: core::slice::SplitNMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::rsplit::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: core::slice::RSplit<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::rsplit_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: core::slice::RSplitMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::rsplitn::<F> ](
    slice: &'a [T],
    n: usize,
    pred: F,
) -> (iter: core::slice::RSplitN<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T) -> bool>[ <[T]>::rsplitn_mut::<F> ](
    slice: &'a mut [T],
    n: usize,
    pred: F,
) -> (iter: core::slice::RSplitNMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T, &T) -> bool>[ <[T]>::chunk_by::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: core::slice::ChunkBy<'a, T, F>)
;

pub assume_specification<'a, T, F: core::ops::FnMut(&T, &T) -> bool>[ <[T]>::chunk_by_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: core::slice::ChunkByMut<'a, T, F>)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<'a, T, R: core::ops::OneSidedRange<usize>>[ <[T]>::split_off::<R> ](
    slice_ref: &mut &'a [T],
    range: R,
) -> (ret: Option<&'a [T]>)
    ensures
        ret.is_none() ==> (*final(slice_ref))@ == (*old(slice_ref))@,
        exists|observed: (core::ops::OneSidedRangeBound, usize)| {
            &&& #[trigger] call_ensures(
                <R as core::ops::OneSidedRange<usize>>::bound, (range,), observed,
            )
            &&& match observed.0 {
                core::ops::OneSidedRangeBound::StartInclusive => {
                    &&& ret.is_some() == (observed.1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(observed.1 as int, (*old(slice_ref))@.len() as int)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(0, observed.1 as int)
                },
                core::ops::OneSidedRangeBound::End => {
                    &&& ret.is_some() == (observed.1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(0, observed.1 as int)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(observed.1 as int, (*old(slice_ref))@.len() as int)
                },
                core::ops::OneSidedRangeBound::EndInclusive => {
                    &&& ret.is_some() == (observed.1 < usize::MAX && observed.1 + 1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(0, observed.1 + 1)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(observed.1 + 1, (*old(slice_ref))@.len() as int)
                },
            }
        },
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<'a, T, R: core::ops::OneSidedRange<usize>>[
    <[T]>::split_off_mut::<R>
](
    slice_ref: &mut &'a mut [T],
    range: R,
) -> (ret: Option<&'a mut [T]>)
    ensures
        ret.is_none() ==> (*final(slice_ref))@ == (*old(slice_ref))@
            && final(*old(slice_ref))@ == final(*final(slice_ref))@,
        exists|observed: (core::ops::OneSidedRangeBound, usize)| {
            &&& #[trigger] call_ensures(
                <R as core::ops::OneSidedRange<usize>>::bound, (range,), observed,
            )
            &&& match observed.0 {
                core::ops::OneSidedRangeBound::StartInclusive => {
                    &&& ret.is_some() == (observed.1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(observed.1 as int, (*old(slice_ref))@.len() as int)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(0, observed.1 as int)
                        && final(*old(slice_ref))@ == final(*final(slice_ref))@ + final(ret.unwrap())@
                },
                core::ops::OneSidedRangeBound::End => {
                    &&& ret.is_some() == (observed.1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(0, observed.1 as int)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(observed.1 as int, (*old(slice_ref))@.len() as int)
                        && final(*old(slice_ref))@ == final(ret.unwrap())@ + final(*final(slice_ref))@
                },
                core::ops::OneSidedRangeBound::EndInclusive => {
                    &&& ret.is_some() == (observed.1 < usize::MAX && observed.1 + 1 <= (*old(slice_ref))@.len())
                    &&& ret.is_some() ==> ret.unwrap()@ == (*old(slice_ref))@.subrange(0, observed.1 + 1)
                        && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(observed.1 + 1, (*old(slice_ref))@.len() as int)
                        && final(*old(slice_ref))@ == final(ret.unwrap())@ + final(*final(slice_ref))@
                },
            }
        },
;

pub assume_specification<'a, T>[ <[T]>::split_off_first ](
    slice_ref: &mut &'a [T],
) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && *ret.unwrap() == (*old(slice_ref))@[0]
            && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(
                1, (*old(slice_ref))@.len() as int,
            ),
;

pub assume_specification<'a, T>[ <[T]>::split_off_first_mut ](
    slice_ref: &mut &'a mut [T],
) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@
            && final(*old(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && *ret.unwrap() == (*old(slice_ref))@[0]
            && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(
                1, (*old(slice_ref))@.len() as int,
            )
            && final(*old(slice_ref))@
                == seq![*final(ret.unwrap())] + final(*final(slice_ref))@,
;

pub assume_specification<'a, T>[ <[T]>::split_off_last ](
    slice_ref: &mut &'a [T],
) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && *ret.unwrap() == (*old(slice_ref))@[(*old(slice_ref))@.len() - 1]
            && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(
                0, (*old(slice_ref))@.len() - 1,
            ),
;

pub assume_specification<'a, T>[ <[T]>::split_off_last_mut ](
    slice_ref: &mut &'a mut [T],
) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@
            && final(*old(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && *ret.unwrap() == (*old(slice_ref))@[(*old(slice_ref))@.len() - 1]
            && (*final(slice_ref))@ == (*old(slice_ref))@.subrange(
                0, (*old(slice_ref))@.len() - 1,
            )
            && final(*old(slice_ref))@
                == final(*final(slice_ref))@ + seq![*final(ret.unwrap())],
;

pub assume_specification<'a>[ <[u8]>::utf8_chunks ](
    slice: &'a [u8],
) -> (iter: core::str::Utf8Chunks<'a>)
;

pub assume_specification<T: core::clone::Clone>[ <[T]>::clone_from_slice ](
    dst: &mut [T],
    src: &[T],
)

    requires
        old(dst)@.len() == src@.len(),
    ensures
        final(dst)@.len() == src@.len(),
        forall|i: int|
            #![trigger final(dst)@[i]]
            0 <= i < src@.len() ==> cloned::<T>(src@[i], final(dst)@[i]),
;

pub assume_specification<T: core::clone::Clone>[ <[T]>::fill ](
    slice: &mut [T],
    value: T,
)

    ensures
        final(slice)@.len() == old(slice)@.len(),
        old(slice)@.len() == 1 ==> final(slice)@ == seq![value],
;

pub assume_specification<T, F: core::ops::FnMut() -> T>[ <[T]>::fill_with::<F> ](
    slice: &mut [T],
    f: F,
)

    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification<T>[ <[T]>::reverse ](
    slice: &mut [T],
)
    ensures
        final(slice)@ == Seq::new(
            old(slice)@.len(), |i: int| old(slice)@[old(slice)@.len() - 1 - i],
        ),
;

pub assume_specification<T>[ <[T]>::rotate_left ](
    slice: &mut [T],
    mid: usize,
)
    requires
        mid <= old(slice)@.len(),
    ensures
        final(slice)@ == old(slice)@.subrange(mid as int, old(slice)@.len() as int)
            + old(slice)@.subrange(0, mid as int),
;

pub assume_specification<T>[ <[T]>::rotate_right ](
    slice: &mut [T],
    k: usize,
)
    requires
        k <= old(slice)@.len(),
    ensures
        final(slice)@ == old(slice)@.subrange(
            old(slice)@.len() - k, old(slice)@.len() as int,
        ) + old(slice)@.subrange(0, old(slice)@.len() - k),
;

pub assume_specification<T>[ <[T]>::swap ](
    slice: &mut [T],
    a: usize,
    b: usize,
)
    requires
        a < old(slice)@.len(),
        b < old(slice)@.len(),
    ensures
        final(slice)@ == old(slice)@.update(a as int, old(slice)@[b as int])
            .update(b as int, old(slice)@[a as int]),
;

pub assume_specification<T>[ <[T]>::swap_with_slice ](
    slice: &mut [T],
    other: &mut [T],
)
    requires
        old(slice)@.len() == old(other)@.len(),
    ensures
        final(slice)@ == old(other)@,
        final(other)@ == old(slice)@,
;

pub assume_specification<T, U>[ <[T]>::align_to::<U> ](
    slice: &[T],
) -> (ret: (&[T], &[U], &[T]))

    requires
        slice@.len() == 0,
    ensures
        ret.0@.len() == 0,
        ret.1@.len() == 0,
        ret.2@.len() == 0,
;

pub assume_specification<T, U>[ <[T]>::align_to_mut::<U> ](
    slice: &mut [T],
) -> (ret: (&mut [T], &mut [U], &mut [T]))

    requires
        old(slice)@.len() == 0,
    ensures
        ret.0@.len() == 0,
        ret.1@.len() == 0,
        ret.2@.len() == 0,
        final(ret.0)@.len() == 0,
        final(ret.1)@.len() == 0,
        final(ret.2)@.len() == 0,
        final(slice)@.len() == 0,
;

pub assume_specification<T, const N: usize>[ <[[T; N]]>::as_flattened ](
    slice: &[[T; N]],
) -> (ret: &[T])

    requires
        core::mem::size_of::<T>() != 0
            || slice@.len() * (N as nat) <= usize::MAX,
    ensures
        ret@ == if N == 0 {
            Seq::empty()
        } else {
            Seq::new(
                slice@.len() * (N as nat),
                |i: int| slice@[i / (N as int)]@[i % (N as int)],
            )
        },
;

pub assume_specification<T, const N: usize>[ <[[T; N]]>::as_flattened_mut ](
    slice: &mut [[T; N]],
) -> (ret: &mut [T])

    requires
        core::mem::size_of::<T>() != 0
            || old(slice)@.len() * (N as nat) <= usize::MAX,
    ensures
        ret@ == if N == 0 {
            Seq::empty()
        } else {
            Seq::new(
                old(slice)@.len() * (N as nat),
                |i: int| old(slice)@[i / (N as int)]@[i % (N as int)],
            )
        },
        final(ret)@.len() == ret@.len(),
        final(slice)@.len() == old(slice)@.len(),
        forall|chunk: int|
            #![trigger final(slice)@[chunk]@]
            0 <= chunk < final(slice)@.len() ==> final(slice)@[chunk]@
                == final(ret)@.subrange(
                    chunk * (N as int),
                    (chunk + 1) * (N as int),
                ),
;

pub assume_specification<T>[ <[T]>::as_mut_ptr ](
    slice: &mut [T],
) -> (ptr: *mut T)

    ensures
        ptr.addr() % core::mem::align_of::<T>() == 0,
        final(slice)@ == old(slice)@,
;

pub assume_specification<T>[ <[T]>::as_mut_ptr_range ](
    slice: &mut [T],
) -> (range: core::ops::Range<*mut T>)

    ensures
        final(slice)@ == old(slice)@,
;

pub assume_specification<T>[ <[T]>::as_ptr ](
    slice: &[T],
) -> (ptr: *const T)

    ensures
        ptr.addr() % core::mem::align_of::<T>() == 0,
;

pub assume_specification<T>[ <[T]>::as_ptr_range ](
    slice: &[T],
) -> (range: core::ops::Range<*const T>)
;

pub assume_specification<T>[ <[core::mem::MaybeUninit<T>]>::assume_init_drop ](
    slice: &mut [core::mem::MaybeUninit<T>],
)

    requires
        old(slice)@.len() == 0,
    ensures
        final(slice)@.len() == 0,
;

pub assume_specification<T>[ <[core::mem::MaybeUninit<T>]>::assume_init_mut ](
    slice: &mut [core::mem::MaybeUninit<T>],
) -> (ret: &mut [T])

    requires
        old(slice)@.len() == 0,
    ensures
        ret@.len() == 0,
        final(ret)@.len() == 0,
        final(slice)@.len() == 0,
;

pub assume_specification<T>[ <[core::mem::MaybeUninit<T>]>::assume_init_ref ](
    slice: &[core::mem::MaybeUninit<T>],
) -> (ret: &[T])

    requires
        slice@.len() == 0,
    ensures
        ret@.len() == 0,
;

pub assume_specification<T>[ <[T]>::element_offset ](
    slice: &[T],
    element: &T,
) -> (ret: Option<usize>)

    requires
        core::mem::size_of::<T>() != 0,
    ensures
        ret.is_some() ==> ret.unwrap() < slice@.len(),
;

pub assume_specification[ <[u8]>::eq_ignore_ascii_case ](
    slice: &[u8],
    other: &[u8],
) -> (ret: bool)
    ensures
        ret <==> slice@.len() == other@.len()
            && (forall|i: int| 0 <= i < slice@.len() ==>
                (if 0x41 <= slice@[i] <= 0x5a { slice@[i] as int + 0x20 }
                    else { slice@[i] as int })
                == (if 0x41 <= other@[i] <= 0x5a { other@[i] as int + 0x20 }
                    else { other@[i] as int })),
;

pub assume_specification<'a>[ <[u8]>::escape_ascii ](
    slice: &'a [u8],
) -> (iter: core::slice::EscapeAscii<'a>)
;

pub assume_specification<'a, T>[ core::slice::from_mut::<T> ](
    value: &'a mut T,
) -> (ret: &'a mut [T])
    ensures
        ret@ == seq![*old(value)],
        final(ret)@ == seq![*final(value)],
;

pub assume_specification<'a, T>[ core::slice::from_raw_parts::<T> ](
    data: *const T,
    len: usize,
) -> (ret: &'a [T])

    requires
        len == 0,
        data.addr() != 0,
        data.addr() % core::mem::align_of::<T>() == 0,
    ensures
        ret@.len() == len,
;

pub assume_specification<'a, T>[ core::slice::from_raw_parts_mut::<T> ](
    data: *mut T,
    len: usize,
) -> (ret: &'a mut [T])

    requires
        len == 0,
        data.addr() != 0,
        data.addr() % core::mem::align_of::<T>() == 0,
    ensures
        ret@.len() == len,
        final(ret)@.len() == len,
;

pub assume_specification<'a, T>[ core::slice::from_ref::<T> ](
    value: &'a T,
) -> (ret: &'a [T])
    ensures
        ret@ == seq![*value],
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<T, I, const N: usize>[ <[T]>::get_disjoint_mut::<I, N> ](
    slice: &mut [T],
    indices: [I; N],
) -> (ret: core::result::Result<
    [&mut <I as core::slice::SliceIndex<[T]>>::Output; N],
    core::slice::GetDisjointMutError,
>) where I: core::slice::GetDisjointMutIndex + core::slice::SliceIndex<[T]>

    ensures
        final(slice)@.len() == old(slice)@.len(),
        ret.is_err() ==> final(slice)@ == old(slice)@,
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<T, I, const N: usize>[ <[T]>::get_disjoint_unchecked_mut::<I, N> ](
    slice: &mut [T],
    indices: [I; N],
) -> (ret: [&mut <I as core::slice::SliceIndex<[T]>>::Output; N])
    where I: core::slice::GetDisjointMutIndex + core::slice::SliceIndex<[T]>

    requires
        N == 0,
    ensures
        final(slice)@ == old(slice)@,
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<T, I>[ <[T]>::get_unchecked::<I> ](
    slice: &[T],
    index: I,
) -> (ret: &<I as core::slice::SliceIndex<[T]>>::Output)
    where I: core::slice::SliceIndex<[T]>

    requires
        index.in_bounds(slice),
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<T, I>[ <[T]>::get_unchecked_mut::<I> ](
    slice: &mut [T],
    index: I,
) -> (ret: &mut <I as core::slice::SliceIndex<[T]>>::Output)
    where I: core::slice::SliceIndex<[T]>

    requires
        index.in_bounds(old(slice)),
    ensures
        final(slice)@.len() == old(slice)@.len(),
;

pub assume_specification[ <[u8]>::is_ascii ](
    slice: &[u8],
) -> (ret: bool)
    ensures
        ret <==> (forall|i: int| 0 <= i < slice@.len() ==> slice@[i] <= 0x7f),
;

pub assume_specification<T: core::cmp::PartialOrd>[ <[T]>::is_sorted ](
    slice: &[T],
) -> (ret: bool)

    ensures
        slice@.len() < 2 ==> ret,
;

pub assume_specification<'a, T, F: core::ops::FnMut(&'a T, &'a T) -> bool>[
    <[T]>::is_sorted_by::<F>
](
    slice: &'a [T],
    compare: F,
) -> (ret: bool)

    ensures
        slice@.len() < 2 ==> ret,
;

pub assume_specification<'a, T, F: core::ops::FnMut(&'a T) -> K, K: core::cmp::PartialOrd>[
    <[T]>::is_sorted_by_key::<F, K>
](
    slice: &'a [T],
    f: F,
) -> (ret: bool)

    ensures
        slice@.len() < 2 ==> ret,
;

pub assume_specification[ <[u8]>::make_ascii_lowercase ](
    slice: &mut [u8],
)
    ensures
        final(slice)@ == Seq::new(old(slice)@.len(), |i: int|
            if 0x41 <= old(slice)@[i] <= 0x5a {
                (old(slice)@[i] as int + 0x20) as u8
            } else {
                old(slice)@[i]
            }),
;

pub assume_specification[ <[u8]>::make_ascii_uppercase ](
    slice: &mut [u8],
)
    ensures
        final(slice)@ == Seq::new(old(slice)@.len(), |i: int|
            if 0x61 <= old(slice)@[i] <= 0x7a {
                (old(slice)@[i] as int - 0x20) as u8
            } else {
                old(slice)@[i]
            }),
;

pub assume_specification<T: core::cmp::Ord>[ <[T]>::select_nth_unstable ](
    slice: &mut [T],
    index: usize,
) -> (ret: (&mut [T], &mut T, &mut [T]))

    requires
        index < old(slice)@.len(),
    ensures
        ret.0@.len() == index,
        ret.2@.len() == old(slice)@.len() - index - 1,
        final(slice)@
            == final(ret.0)@ + seq![*final(ret.1)] + final(ret.2)@,
        final(ret.0)@.len() == ret.0@.len(),
        final(ret.2)@.len() == ret.2@.len(),
;

pub assume_specification<T, F: core::ops::FnMut(&T, &T) -> core::cmp::Ordering>[
    <[T]>::select_nth_unstable_by::<F>
](
    slice: &mut [T],
    index: usize,
    compare: F,
) -> (ret: (&mut [T], &mut T, &mut [T]))

    requires
        index < old(slice)@.len(),
    ensures
        ret.0@.len() == index,
        ret.2@.len() == old(slice)@.len() - index - 1,
        final(slice)@
            == final(ret.0)@ + seq![*final(ret.1)] + final(ret.2)@,
        final(ret.0)@.len() == ret.0@.len(),
        final(ret.2)@.len() == ret.2@.len(),
;

pub assume_specification<T, K: core::cmp::Ord, F: core::ops::FnMut(&T) -> K>[
    <[T]>::select_nth_unstable_by_key::<K, F>
](
    slice: &mut [T],
    index: usize,
    f: F,
) -> (ret: (&mut [T], &mut T, &mut [T]))

    requires
        index < old(slice)@.len(),
    ensures
        ret.0@.len() == index,
        ret.2@.len() == old(slice)@.len() - index - 1,
        final(slice)@
            == final(ret.0)@ + seq![*final(ret.1)] + final(ret.2)@,
        final(ret.0)@.len() == ret.0@.len(),
        final(ret.2)@.len() == ret.2@.len(),
;

pub assume_specification<T: core::cmp::Ord>[ <[T]>::sort_unstable ](
    slice: &mut [T],
)

    ensures
        final(slice)@.len() == old(slice)@.len(),
        old(slice)@.len() < 2 ==> final(slice)@ == old(slice)@,
;

pub assume_specification<T, F: core::ops::FnMut(&T, &T) -> core::cmp::Ordering>[
    <[T]>::sort_unstable_by::<F>
](
    slice: &mut [T],
    compare: F,
)

    ensures
        final(slice)@.len() == old(slice)@.len(),
        old(slice)@.len() < 2 ==> final(slice)@ == old(slice)@,
;

pub assume_specification<T, K: core::cmp::Ord, F: core::ops::FnMut(&T) -> K>[
    <[T]>::sort_unstable_by_key::<K, F>
](
    slice: &mut [T],
    f: F,
)

    ensures
        final(slice)@.len() == old(slice)@.len(),
        old(slice)@.len() < 2 ==> final(slice)@ == old(slice)@,
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<
    'a,
    'p,
    T: core::cmp::PartialEq,
    P: core::slice::SlicePattern<Item = T> + ?Sized,
>[
    <[T]>::strip_prefix::<P>
](
    slice: &'a [T],
    prefix: &'p P,
) -> (ret: Option<&'a [T]>)

    ensures
        ret.is_some() ==> exists|cut: int| {
            &&& 0 <= cut <= slice@.len()
            &&& ret.unwrap()@ == slice@.subrange(cut, slice@.len() as int)
        },
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<
    'a,
    'p,
    T: core::cmp::PartialEq,
    P: core::slice::SlicePattern<Item = T> + ?Sized,
>[
    <[T]>::strip_suffix::<P>
](
    slice: &'a [T],
    suffix: &'p P,
) -> (ret: Option<&'a [T]>)

    ensures
        ret.is_some() ==> exists|cut: int| {
            &&& 0 <= cut <= slice@.len()
            &&& ret.unwrap()@ == slice@.subrange(0, cut)
        },
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<
    'a,
    'p,
    's,
    T: core::cmp::PartialEq,
    S: core::slice::SlicePattern<Item = T> + ?Sized,
    P: core::slice::SlicePattern<Item = T> + ?Sized,
>[ <[T]>::strip_circumfix::<S, P> ](
    slice: &'a [T],
    prefix: &'p P,
    suffix: &'s S,
) -> (ret: Option<&'a [T]>)

    ensures
        ret.is_some() ==> exists|lo: int, hi: int| {
            &&& 0 <= lo <= hi <= slice@.len()
            &&& ret.unwrap()@ == slice@.subrange(lo, hi)
        },
;

pub assume_specification<T>[ <[T]>::subslice_range ](
    slice: &[T],
    subslice: &[T],
) -> (ret: Option<core::range::Range<usize>>)

    requires
        core::mem::size_of::<T>() != 0,
    ensures
        ret.is_some() ==> subslice@.len() <= slice@.len(),
;

pub assume_specification[ <[u8]>::trim_ascii ](
    slice: &[u8],
) -> (ret: &[u8])
    ensures
        exists|start: int, end: int|
            0 <= start <= end <= slice@.len()
            && ret@ == slice@.subrange(start, end)
            && (forall|i: int| 0 <= i < start ==>
                (slice@[i] == 0x09 || slice@[i] == 0x0a || slice@[i] == 0x0c
                    || slice@[i] == 0x0d || slice@[i] == 0x20))
            && (forall|i: int| end <= i < slice@.len() ==>
                (slice@[i] == 0x09 || slice@[i] == 0x0a || slice@[i] == 0x0c
                    || slice@[i] == 0x0d || slice@[i] == 0x20))
            && (start < slice@.len() ==> !(slice@[start] == 0x09
                || slice@[start] == 0x0a || slice@[start] == 0x0c
                || slice@[start] == 0x0d || slice@[start] == 0x20))
            && (start < end ==> !(slice@[end - 1] == 0x09
                || slice@[end - 1] == 0x0a || slice@[end - 1] == 0x0c
                || slice@[end - 1] == 0x0d || slice@[end - 1] == 0x20)),
;

pub assume_specification[ <[u8]>::trim_ascii_end ](
    slice: &[u8],
) -> (ret: &[u8])
    ensures
        ret@.len() <= slice@.len(),
        ret@ == slice@.subrange(0, ret@.len() as int),
        forall|i: int| ret@.len() <= i < slice@.len() ==>
            (slice@[i] == 0x09 || slice@[i] == 0x0a || slice@[i] == 0x0c
                || slice@[i] == 0x0d || slice@[i] == 0x20),
        ret@.len() > 0 ==> !(ret@[ret@.len() - 1] == 0x09
            || ret@[ret@.len() - 1] == 0x0a || ret@[ret@.len() - 1] == 0x0c
            || ret@[ret@.len() - 1] == 0x0d || ret@[ret@.len() - 1] == 0x20),
;

pub assume_specification[ <[u8]>::trim_ascii_start ](
    slice: &[u8],
) -> (ret: &[u8])
    ensures
        ret@.len() <= slice@.len(),
        ret@ == slice@.subrange(
            (slice@.len() - ret@.len()) as int, slice@.len() as int,
        ),
        forall|i: int| 0 <= i < slice@.len() - ret@.len() ==>
            (slice@[i] == 0x09 || slice@[i] == 0x0a || slice@[i] == 0x0c
                || slice@[i] == 0x0d || slice@[i] == 0x20),
        ret@.len() > 0 ==> !(ret@[0] == 0x09 || ret@[0] == 0x0a
            || ret@[0] == 0x0c || ret@[0] == 0x0d || ret@[0] == 0x20),
;

pub assume_specification<'a, 'b, T: core::clone::Clone>[
    <[core::mem::MaybeUninit<T>]>::write_clone_of_slice
](
    slice: &'a mut [core::mem::MaybeUninit<T>],
    src: &'b [T],
) -> (ret: &'a mut [T])

    requires
        old(slice)@.len() == src@.len(),
    ensures
        ret@.len() == src@.len(),
        forall|i: int|
            #![trigger ret@[i]]
            0 <= i < src@.len() ==> cloned::<T>(src@[i], ret@[i]),
        final(ret)@.len() == src@.len(),
;

pub assume_specification<'a, 'b, T: core::marker::Copy>[
    <[core::mem::MaybeUninit<T>]>::write_copy_of_slice
](
    slice: &'a mut [core::mem::MaybeUninit<T>],
    src: &'b [T],
) -> (ret: &'a mut [T])

    requires
        old(slice)@.len() == src@.len(),
    ensures
        ret@ == src@,
        final(ret)@.len() == src@.len(),
;

} // verus!
