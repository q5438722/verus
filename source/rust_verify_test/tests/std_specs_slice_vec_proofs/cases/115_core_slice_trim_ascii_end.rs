#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::trim_ascii_end
// Source: core/src/slice/ascii.rs:266-278
// Source item sha256: 68e32185388f1041ca1b0731847a298f3216158d80a664301c19ce74d930a94b
// Dependency manifest: proof_manifests/115_core_slice_trim_ascii_end/dependency_assumption_manifest.json

use vstd::prelude::*;
use vstd::seq::*;

verus! {

pub open spec fn ascii_is_whitespace(byte: u8) -> bool {
    byte == 0x09u8
        || byte == 0x0au8
        || byte == 0x0cu8
        || byte == 0x0du8
        || byte == 0x20u8
}

pub open spec fn ascii_trim_end_boundary(seq: Seq<u8>, i: int) -> bool {
    0 <= i <= seq.len()
        && (forall|j: int| i <= j < seq.len() ==> #[trigger] ascii_is_whitespace(seq[j]))
        && (0 < i ==> !ascii_is_whitespace(seq[i - 1]))
}

pub open spec fn ascii_trim_end_index(seq: Seq<u8>) -> int {
    choose|i: int| #[trigger] ascii_trim_end_boundary(seq, i)
}

pub open spec fn ascii_trim_end_result(seq: Seq<u8>, ret: &[u8]) -> bool {
    0 <= ascii_trim_end_index(seq) <= seq.len()
        && ret@ == seq.subrange(0, ascii_trim_end_index(seq))
        && (forall|i: int| #![auto] ascii_trim_end_index(seq) <= i < seq.len() ==> ascii_is_whitespace(seq[i]))
        && (0 < ascii_trim_end_index(seq) ==> !ascii_is_whitespace(seq[ascii_trim_end_index(seq) - 1]))
}

const fn byte_is_ascii_whitespace(byte: u8) -> (ret: bool)
    ensures
        ret <==> ascii_is_whitespace(byte),
{
    byte == 0x09u8
        || byte == 0x0au8
        || byte == 0x0cu8
        || byte == 0x0du8
        || byte == 0x20u8
}

proof fn lemma_ascii_trim_end_boundary_unique(seq: Seq<u8>, i: int, j: int)
    requires
        ascii_trim_end_boundary(seq, i),
        ascii_trim_end_boundary(seq, j),
    ensures
        i == j,
{
    if i < j {
        assert(0 < j);
        assert(i <= j - 1);
        assert(j - 1 < seq.len());
        assert(ascii_is_whitespace(seq[j - 1]));
        assert(!ascii_is_whitespace(seq[j - 1]));
        assert(false);
    } else if j < i {
        assert(0 < i);
        assert(j <= i - 1);
        assert(i - 1 < seq.len());
        assert(ascii_is_whitespace(seq[i - 1]));
        assert(!ascii_is_whitespace(seq[i - 1]));
        assert(false);
    }
}

proof fn lemma_ascii_trim_end_index_matches_boundary(seq: Seq<u8>, i: int)
    requires
        ascii_trim_end_boundary(seq, i),
    ensures
        ascii_trim_end_index(seq) == i,
{
    let chosen = ascii_trim_end_index(seq);
    assert(ascii_trim_end_boundary(seq, chosen)) by {
        reveal(ascii_trim_end_index);
        assert(exists|j: int| ascii_trim_end_boundary(seq, j)) by {
            assert(ascii_trim_end_boundary(seq, i));
        }
    }
    lemma_ascii_trim_end_boundary_unique(seq, chosen, i);
}

proof fn lemma_ascii_trim_end_result_from_boundary(seq: Seq<u8>, ret: &[u8], i: int)
    requires
        ascii_trim_end_boundary(seq, i),
        ret@ == seq.subrange(0, i),
    ensures
        ascii_trim_end_result(seq, ret),
{
    lemma_ascii_trim_end_index_matches_boundary(seq, i);
}

pub const fn trim_ascii_end<'a>(slice: &'a [u8]) -> (ret: &'a [u8])
    ensures
        ascii_trim_end_result(slice@, ret),
{
    let ghost source = slice@;
    let mut bytes = slice;
    proof {
        assert(bytes@ =~= source.subrange(0, source.len() as int));
    }

    loop
        invariant
            bytes@.len() <= source.len(),
            bytes@ == source.subrange(0, bytes@.len() as int),
            forall|j: int| #![auto] j >= bytes@.len() && source.len() > j ==> ascii_is_whitespace(source[j]),
        ensures
            bytes@.len() == 0 || !ascii_is_whitespace(source[(bytes@.len() as int) - 1]),
        decreases bytes.len()
    {
        let len = bytes.len();
        proof {
            vstd::slice::axiom_spec_len(bytes);
            assert(len == bytes@.len());
        }
        if len == 0 {
            break;
        }

        let ghost old_bytes = bytes@;
        let ghost old_len: int = old_bytes.len() as int;
        let split = len - 1;
        let (rest, tail) = bytes.split_at(split);
        proof {
            assert(len > 0);
            assert(old_len > 0);
            assert(split as int == old_len - 1);
            old_bytes.lemma_split_at(split as int);
            assert(rest@ =~= old_bytes.subrange(0, split as int));
            assert(tail@ =~= old_bytes.subrange(split as int, old_len));
            assert(tail@.len() == 1);
            assert(tail@[0] == old_bytes[(old_len - 1) as int]);
            assert(old_bytes == source.subrange(0, old_len as int));
            vstd::seq::lemma_seq_subrange_composition(
                source,
                0,
                old_len,
                0,
                old_len - 1,
            );
            vstd::seq::lemma_seq_subrange_index(
                source,
                0,
                old_len,
                old_len - 1,
            );
            assert(rest@ == source.subrange(0, old_len - 1));
            assert(old_bytes[(old_len - 1) as int] == source[(old_len - 1) as int]);
            vstd::seq::lemma_seq_subrange_len(old_bytes, 0, old_len - 1);
            assert(rest@.len() == old_len - 1);
        }
        let last = &tail[0];
        proof {
            assert(*last == tail@[0]);
            assert(*last == source[(old_len - 1) as int]);
        }
        if byte_is_ascii_whitespace(*last) {
            proof {
                assert(ascii_is_whitespace(source[(old_len - 1) as int]));
                assert forall|j: int| #![auto]
                    j >= rest@.len() && source.len() > j
                    implies ascii_is_whitespace(source[j]) by {
                    if j < old_len {
                        assert(j == old_len - 1);
                        assert(ascii_is_whitespace(source[(old_len - 1) as int]));
                    } else {
                        assert(j >= old_len);
                    }
                }
            }
            bytes = rest;
        } else {
            proof {
                assert(!ascii_is_whitespace(source[(old_len - 1) as int]));
                assert(bytes@.len() > 0);
                assert(!ascii_is_whitespace(source[(bytes@.len() as int) - 1]));
            }
            break;
        }
    }

    proof {
        let end = bytes@.len() as int;
        assert(bytes@ == source.subrange(0, end));
        assert forall|j: int| #![auto] end <= j < source.len() implies ascii_is_whitespace(source[j]) by {
            assert(j >= bytes@.len() && source.len() > j);
        }
        if end > 0 {
            assert(!ascii_is_whitespace(source[end - 1]));
        }
        assert(ascii_trim_end_boundary(source, end));
        lemma_ascii_trim_end_result_from_boundary(source, bytes, end);
    }

    bytes
}

}
