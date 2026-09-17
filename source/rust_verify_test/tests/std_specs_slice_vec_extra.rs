#![feature(rustc_private)]

#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_slice_vec_extra_specs verus_code! {
        use vstd::prelude::*;

        fn split_at_mut_unchecked_write<T>(
            slice: &mut [T],
            mid: usize,
            left: T,
            right: T,
        )
            requires
                0 < mid < old(slice)@.len(),
            ensures
                final(slice)@ == old(slice)@.update(0, left).update(mid as int, right),
        {
            let ghost before = slice@;
            {
                let (prefix, suffix) = unsafe { slice.split_at_mut_unchecked(mid) };
                prefix[0] = left;
                suffix[0] = right;
            }
            assert(slice@ =~= before.update(0, left).update(mid as int, right));
        }

        fn first_chunk_shape<T, const N: usize>(slice: &[T]) {
            let result = slice.first_chunk::<N>();
            if N <= slice.len() {
                assert(result.is_some());
                assert(result.unwrap()@ == slice@.subrange(0, N as int));
            } else {
                assert(result.is_none());
            }
        }

        fn flattened_shape<T, const N: usize>(slice: &[[T; N]])
            requires
                core::mem::size_of::<T>() != 0
                    || slice@.len() * (N as nat) <= usize::MAX,
        {
            let flattened = slice.as_flattened();
            assert(flattened@.len() == slice@.len() * N);
        }

        fn slice_pointer_is_aligned<T>(slice: &[T]) {
            let pointer = slice.as_ptr();
            assert(pointer.addr() % core::mem::align_of::<T>() == 0);
        }

        fn push_mut_write<T>(vec: &mut Vec<T>, value: T, replacement: T)
            ensures
                final(vec)@ == old(vec)@.push(replacement),
        {
            let slot = vec.push_mut(value);
            *slot = replacement;
        }

        fn insert_mut_write<T>(
            vec: &mut Vec<T>,
            index: usize,
            value: T,
            replacement: T,
        )
            requires
                index <= old(vec)@.len(),
            ensures
                final(vec)@ == old(vec)@.insert(index as int, replacement),
        {
            let slot = vec.insert_mut(index, value);
            *slot = replacement;
        }

        fn set_len_shrink<T>(vec: &mut Vec<T>, new_len: usize)
            requires
                new_len <= old(vec)@.len(),
            ensures
                final(vec)@ == old(vec)@.subrange(0, new_len as int),
        {
            unsafe {
                vec.set_len(new_len);
            }
        }

        fn dedup_does_not_grow<T: core::cmp::PartialEq>(vec: &mut Vec<T>)
            ensures
                final(vec)@.len() <= old(vec)@.len(),
        {
            vec.dedup();
        }

        fn resize_with_has_requested_length<T, F: core::ops::FnMut() -> T>(
            vec: &mut Vec<T>,
            new_len: usize,
            generator: F,
        )
            ensures
                final(vec)@.len() == new_len,
        {
            vec.resize_with(new_len, generator);
        }

        fn vec_pointer_preserves_values<T>(vec: &mut Vec<T>)
            ensures
                final(vec)@ == old(vec)@,
        {
            let pointer = vec.as_mut_ptr();
            assert(pointer.addr() % core::mem::align_of::<T>() == 0);
        }
    } => Ok(())
}

#[test]
fn added_modules_are_zero_uf_and_helper_free() {
    let slice = include_str!("../../vstd/std_specs/slice_extra.rs");
    let vec = include_str!("../../vstd/std_specs/vec_extra.rs");

    for source in [slice, vec] {
        assert!(!source.contains("uninterp spec fn"));
        assert!(!source.contains("pub open spec fn"));
        assert!(!source.contains("admit()"));
        assert!(!source.contains("assume("));
    }

    assert_eq!(slice.matches("pub assume_specification").count(), 118);
    assert_eq!(vec.matches("pub assume_specification").count(), 24);
}
