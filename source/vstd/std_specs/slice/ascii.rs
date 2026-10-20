use crate::prelude::*;
use crate::std_specs::iter::IteratorSpec;
use core::slice::*;

verus! {

pub type Parts = (Seq<u8>, Seq<u8>, Seq<u8>);

pub open spec fn contents(parts: Parts) -> Seq<u8> {
    parts.0 + escaped(parts.1) + parts.2
}

pub open spec fn initial(bytes: Seq<u8>) -> Parts {
    (Seq::empty(), bytes, Seq::empty())
}

pub open spec fn front_parts(p: Parts) -> Parts {
    if p.0.len() > 0 {
        (p.0.drop_first(), p.1, p.2)
    } else if p.1.len() > 0 {
        (escape_byte(p.1[0]).drop_first(), p.1.drop_first(), p.2)
    } else {
        (
            Seq::empty(),
            p.1,
            if p.2.len() == 0 {
                p.2
            } else {
                p.2.drop_first()
            },
        )
    }
}

pub open spec fn back_parts(p: Parts) -> Parts {
    if p.2.len() > 0 {
        (p.0, p.1, p.2.drop_last())
    } else if p.1.len() > 0 {
        (p.0, p.1.drop_last(), escape_byte(p.1.last()).drop_last())
    } else {
        (
            if p.0.len() == 0 {
                p.0
            } else {
                p.0.drop_last()
            },
            p.1,
            Seq::empty(),
        )
    }
}

pub open spec fn hex_digit(n: int) -> u8 {
    if n < 10 {
        (48 + n) as u8
    } else {
        (87 + n) as u8
    }
}

pub open spec fn escape_byte(b: u8) -> Seq<u8> {
    if b == 9 {
        seq![92u8, 116u8]
    } else if b == 13 {
        seq![92u8, 114u8]
    } else if b == 10 {
        seq![92u8, 110u8]
    } else if b == 92 {
        seq![92u8, 92u8]
    } else if b == 39 {
        seq![92u8, 39u8]
    } else if b == 34 {
        seq![92u8, 34u8]
    } else if 32 <= b <= 126 {
        seq![b]
    } else {
        seq![92u8, 120u8, hex_digit(b as int / 16), hex_digit(b as int % 16)]
    }
}

pub open spec fn escaped(bytes: Seq<u8>) -> Seq<u8> {
    bytes.flat_map(|b: u8| escape_byte(b))
}

pub open spec fn hint_from_parts(front: Seq<u8>, outer: Seq<u8>, back: Seq<u8>) -> (
    usize,
    Option<usize>,
) {
    let buffered = front.len() + back.len();
    (
        if buffered <= usize::MAX {
            buffered as usize
        } else {
            usize::MAX
        },
        if outer.len() == 0 && buffered <= usize::MAX {
            Some(buffered as usize)
        } else {
            None
        },
    )
}

#[verifier::prophetic]
pub uninterp spec fn view(iter: EscapeAscii<'_>) -> Parts;

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExEscapeAscii<'a>(EscapeAscii<'a>);

pub assume_specification[ <[u8]>::escape_ascii ](bytes: &[u8]) -> (result: EscapeAscii<'_>)
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
;

pub assume_specification<'a>[ <EscapeAscii<'a> as Iterator>::next ](
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
;

pub assume_specification<'a>[ <EscapeAscii<'a> as DoubleEndedIterator>::next_back ](
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
;

pub assume_specification<'a>[ <EscapeAscii<'a> as Iterator>::last ](
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
;

pub assume_specification<'a>[ <EscapeAscii<'a> as Iterator>::size_hint ](
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
;

pub open spec fn is_ascii(bytes: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < bytes.len() ==> #[trigger] bytes[i] < 128
}

pub assume_specification[ <[u8]>::is_ascii ](bytes: &[u8]) -> (result: bool)
    ensures
        result == is_ascii(bytes@),
;

pub assume_specification<'a>[ <EscapeAscii<'a> as Clone>::clone ](
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
;

} // verus!
