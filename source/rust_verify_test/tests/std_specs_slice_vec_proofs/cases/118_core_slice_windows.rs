#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::windows
// Source: core/src/slice/mod.rs:1115-1118 and core/src/slice/iter.rs:1331-1340
// Source item sha256: ed931884cc8fb0445669da6f6430711f8fcb0484ef814f865ce6502806ea4666
// Dependency manifest: proof_manifests/118_core_slice_windows/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remaining: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub struct NonZero {
    pub value: usize,
}

pub enum NonZeroCandidate {
    Some(NonZero),
    None,
}

impl NonZero {
    pub const fn new(value: usize) -> (ret: NonZeroCandidate)
        ensures
            value != 0 ==> ret is Some,
            value == 0 ==> ret is None,
            ret is Some ==> ret->0.value == value && ret->0.value != 0,
    {
        if value == 0 {
            NonZeroCandidate::None
        } else {
            NonZeroCandidate::Some(NonZero { value })
        }
    }

    pub closed spec fn spec_value(self) -> int {
        self.value as int
    }
}

impl NonZeroCandidate {
    pub const fn expect(self, _message: &str) -> (ret: NonZero)
        requires
            self is Some,
            self->0.value != 0,
        ensures
            ret.value == self->0.value,
            ret.value != 0,
    {
        match self {
            NonZeroCandidate::Some(size) => {
                proof {
                    assert(size.value != 0);
                }
                size
            },
            NonZeroCandidate::None => {
                proof {
                    assert(false);
                }
                NonZero { value: 1 }
            },
        }
    }
}

pub struct Windows<'a, T: 'a> {
    v: &'a [T],
    size: NonZero,
}

pub closed spec fn slice_iterator_view<'a, T>(iter: Windows<'a, T>) -> SliceIteratorView<T> {
    SliceIteratorView {
        source: iter.v@,
        yielded_prefix: Seq::empty(),
        remaining: iter.v@,
        remainder: Seq::empty(),
        chunk_size: iter.size.spec_value(),
        reverse: false,
    }
}

impl<'a, T> Windows<'a, T> {
    pub const fn new(slice: &'a [T], size: NonZero) -> (ret: Self)
        ensures
            slice_iterator_view(ret).source == slice@,
            slice_iterator_view(ret).remaining == slice@,
            slice_iterator_view(ret).yielded_prefix.len() == 0,
            slice_iterator_view(ret).remainder.len() == 0,
            slice_iterator_view(ret).chunk_size == size.spec_value(),
            !slice_iterator_view(ret).reverse,
    {
        let ret = Self { v: slice, size };
        proof {
            reveal(slice_iterator_view);
        }
        ret
    }
}

pub const fn windows<'a, T>(slice: &'a [T], size: usize) -> (iter: Windows<'a, T>)
    requires
        size != 0,
    ensures
        slice_iterator_view(iter).source == slice@,
        slice_iterator_view(iter).remaining == slice@,
        slice_iterator_view(iter).yielded_prefix.len() == 0,
        slice_iterator_view(iter).remainder.len() == 0,
        slice_iterator_view(iter).chunk_size == size as int,
        !slice_iterator_view(iter).reverse,
{
    let size = NonZero::new(size).expect("window size must be non-zero");
    Windows::new(slice, size)
}

}
