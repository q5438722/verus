#![allow(dead_code, unused_imports, unused_variables)]
// Target-specific Verus implementation harness.
// Target: core::slice::trim_ascii_start
// Source: core/src/slice/ascii.rs:237-249
// Source item sha256: 7ba3fc3f1435f90eaacea528726c4bac3aba3ac2811679fe61b51ea7ef440197
// Dependency manifest: proof_manifests/116_core_slice_trim_ascii_start/dependency_assumption_manifest.json

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

pub open spec fn ascii_trim_start_boundary(seq: Seq<u8>, i: int) -> bool {
    0 <= i <= seq.len()
        && (forall|j: int| 0 <= j < i ==> #[trigger] ascii_is_whitespace(seq[j]))
        && (i < seq.len() ==> !ascii_is_whitespace(seq[i]))
}

pub open spec fn ascii_trim_start_index(seq: Seq<u8>) -> int {
    choose|i: int| #[trigger] ascii_trim_start_boundary(seq, i)
}

pub open spec fn ascii_trim_start_result(seq: Seq<u8>, ret: &[u8]) -> bool {
    0 <= ascii_trim_start_index(seq) <= seq.len()
        && ret@ == seq.subrange(ascii_trim_start_index(seq), seq.len() as int)
        && (forall|i: int| 0 <= i < ascii_trim_start_index(seq) ==> ascii_is_whitespace(seq[i]))
        && (ascii_trim_start_index(seq) < seq.len() ==> !ascii_is_whitespace(seq[ascii_trim_start_index(seq)]))
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

proof fn lemma_ascii_trim_start_boundary_unique(seq: Seq<u8>, i: int, j: int)
    requires
        ascii_trim_start_boundary(seq, i),
        ascii_trim_start_boundary(seq, j),
    ensures
        i == j,
{
    if i < j {
        assert(i < seq.len());
        assert(ascii_is_whitespace(seq[i]));
        assert(!ascii_is_whitespace(seq[i]));
        assert(false);
    } else if j < i {
        assert(j < seq.len());
        assert(ascii_is_whitespace(seq[j]));
        assert(!ascii_is_whitespace(seq[j]));
        assert(false);
    }
}

proof fn lemma_ascii_trim_start_index_matches_boundary(seq: Seq<u8>, i: int)
    requires
        ascii_trim_start_boundary(seq, i),
    ensures
        ascii_trim_start_index(seq) == i,
{
    let chosen = ascii_trim_start_index(seq);
    assert(ascii_trim_start_boundary(seq, chosen)) by {
        reveal(ascii_trim_start_index);
        assert(exists|j: int| ascii_trim_start_boundary(seq, j)) by {
            assert(ascii_trim_start_boundary(seq, i));
        }
    }
    lemma_ascii_trim_start_boundary_unique(seq, chosen, i);
}

proof fn lemma_ascii_trim_start_result_from_boundary(seq: Seq<u8>, ret: &[u8], i: int)
    requires
        ascii_trim_start_boundary(seq, i),
        ret@ == seq.subrange(i, seq.len() as int),
    ensures
        ascii_trim_start_result(seq, ret),
{
    lemma_ascii_trim_start_index_matches_boundary(seq, i);
}

pub const fn trim_ascii_start<'a>(slice: &'a [u8]) -> (ret: &'a [u8])
    ensures
        ascii_trim_start_result(slice@, ret),
{
    let ghost source = slice@;
    let mut bytes = slice;
    proof {
        assert(bytes@ =~= source.subrange(0, source.len() as int));
    }

    loop
        invariant
            bytes@.len() <= source.len(),
            bytes@ == source.subrange(source.len() as int - bytes@.len() as int, source.len() as int),
            forall|j: int| #![auto] 0 <= j < source.len() as int - bytes@.len() as int
                ==> ascii_is_whitespace(source[j]),
        ensures
            bytes@.len() == 0
                || !ascii_is_whitespace(source[source.len() as int - bytes@.len() as int]),
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
        let ghost prefix_len: int = source.len() as int - old_len;
        proof {
            assert(old_len > 0);
            assert(prefix_len == source.len() as int - bytes@.len() as int);
        }
        let (head, rest) = bytes.split_at(1);
        proof {
            assert(1 <= len);
            assert(1 <= old_len);
            old_bytes.lemma_split_at(1);
            assert(head@ =~= old_bytes.subrange(0, 1));
            assert(rest@ =~= old_bytes.subrange(1, old_len));
            assert(head@.len() == 1);
            assert(head@[0] == old_bytes[0]);
            assert(old_bytes == source.subrange(prefix_len, source.len() as int));
            vstd::seq::lemma_seq_subrange_composition(
                source,
                prefix_len,
                source.len() as int,
                0,
                1,
            );
            vstd::seq::lemma_seq_subrange_index(
                source,
                prefix_len,
                source.len() as int,
                0,
            );
            assert(head@ == source.subrange(prefix_len, prefix_len + 1));
            assert(old_bytes[0] == source[prefix_len]);
            vstd::seq::lemma_seq_subrange_composition(
                source,
                prefix_len,
                source.len() as int,
                1,
                old_len,
            );
            assert(rest@ == source.subrange(prefix_len + 1, source.len() as int));
            vstd::seq::lemma_seq_subrange_len(old_bytes, 1, old_len);
            assert(rest@.len() == old_len - 1);
            assert(source.len() as int - rest@.len() as int == prefix_len + 1);
        }
        let first = &head[0];
        proof {
            assert(*first == head@[0]);
            assert(*first == source[prefix_len]);
        }
        if byte_is_ascii_whitespace(*first) {
            proof {
                assert(ascii_is_whitespace(source[prefix_len]));
                assert forall|j: int| #![auto]
                    0 <= j < source.len() as int - rest@.len() as int
                    implies ascii_is_whitespace(source[j]) by {
                    assert(source.len() as int - rest@.len() as int == prefix_len + 1);
                    if j < prefix_len {
                        assert(j < source.len() as int - old_bytes.len() as int);
                    } else {
                        assert(j == prefix_len);
                        assert(ascii_is_whitespace(source[prefix_len]));
                    }
                }
            }
            bytes = rest;
        } else {
            proof {
                assert(!ascii_is_whitespace(source[prefix_len]));
                assert(bytes@.len() > 0);
                assert(prefix_len == source.len() as int - bytes@.len() as int);
                assert(!ascii_is_whitespace(source[source.len() as int - bytes@.len() as int]));
            }
            break;
        }
    }

    proof {
        let start: int = source.len() as int - bytes@.len() as int;
        assert(bytes@ == source.subrange(start, source.len() as int));
        assert forall|j: int| #![auto] 0 <= j < start implies ascii_is_whitespace(source[j]) by {
            assert(j < source.len() as int - bytes@.len() as int);
        }
        if start < source.len() {
            assert(bytes@.len() > 0);
            assert(!ascii_is_whitespace(source[start]));
        }
        assert(ascii_trim_start_boundary(source, start));
        lemma_ascii_trim_start_result_from_boundary(source, bytes, start);
    }

    bytes
}

}
