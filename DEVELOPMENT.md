# Development

## API parity with `[T]`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Box<[T]>` | `new_uninit_slice` | ⛔️ | foreign type |
| `Box<[T]>` | `new_zeroed_slice` | ⛔️ | foreign type |
| `Box<[T]>` | `try_new_uninit_slice` | ⛔️ | nightly-only |
| `Box<[T]>` | `try_new_zeroed_slice` | ⛔️ | nightly-only |
| `Box<[T], A>` | `new_uninit_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `new_zeroed_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `try_new_uninit_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `try_new_zeroed_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `into_array` | ⛔️ | nightly-only |
| `Box<[MaybeUninit<T>], A>` | `assume_init` | ⛔️ | foreign type |
| `[MaybeUninit<T>]` | `write_copy_of_slice` | ✅ | `slice/mod.rs` |
| `[MaybeUninit<T>]` | `write_clone_of_slice` | ✅ | `slice/mod.rs` |
| `[MaybeUninit<T>]` | `write_filled` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_with` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_default` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_iter` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `as_bytes` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `as_bytes_mut` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `assume_init_drop` | ✅ | `slice/mod.rs` |
| `[MaybeUninit<T>]` | `assume_init_ref` | ✅ | `slice/mod.rs` |
| `[MaybeUninit<T>]` | `assume_init_mut` | ✅ | `slice/mod.rs` |
| `[AsciiChar]` | `as_str` | ⛔️ | nightly-only |
| `[AsciiChar]` | `as_bytes` | ⛔️ | nightly-only |
| `[u8]` | `is_ascii` | ✅ | `slice/mod.rs` |
| `[u8]` | `as_ascii` | ⛔️ | nightly-only |
| `[u8]` | `as_ascii_unchecked` | ⛔️ | nightly-only |
| `[u8]` | `eq_ignore_ascii_case` | ✅ | `slice/mod.rs` |
| `[u8]` | `make_ascii_uppercase` | ✅ | `slice/mod.rs` |
| `[u8]` | `make_ascii_lowercase` | ✅ | `slice/mod.rs` |
| `[u8]` | `escape_ascii` | ✅ | `slice/mod.rs` |
| `[u8]` | `trim_ascii_start` | ✅ | `slice/mod.rs` |
| `[u8]` | `trim_ascii_end` | ✅ | `slice/mod.rs` |
| `[u8]` | `trim_ascii` | ✅ | `slice/mod.rs` |
| `[u8]` | `split_ascii_whitespace` | ⛔️ | nightly-only |
| `[T]` | `len` | ✅ | `slice/mod.rs` |
| `[T]` | `is_empty` | ✅ | `slice/mod.rs` |
| `[T]` | `first` | ✅ | `slice/mod.rs` |
| `[T]` | `first_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_first` | ✅ | `slice/mod.rs` |
| `[T]` | `split_first_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_last` | ✅ | `slice/mod.rs` |
| `[T]` | `split_last_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `last` | ✅ | `slice/mod.rs` |
| `[T]` | `last_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `first_chunk` | ✅ | `slice/mod.rs` |
| `[T]` | `first_chunk_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_first_chunk` | ✅ | `slice/mod.rs` |
| `[T]` | `split_first_chunk_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_last_chunk` | ✅ | `slice/mod.rs` |
| `[T]` | `split_last_chunk_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `last_chunk` | ✅ | `slice/mod.rs` |
| `[T]` | `last_chunk_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `get` | ✅ | `slice/mod.rs` |
| `[T]` | `get_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `get_unchecked` | ✅ | `slice/mod.rs` |
| `[T]` | `get_unchecked_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `as_ptr` | ✅ | `slice/mod.rs` |
| `[T]` | `as_mut_ptr` | ✅ | `slice/mod.rs` |
| `[T]` | `as_ptr_range` | ✅ | `slice/mod.rs` |
| `[T]` | `as_mut_ptr_range` | ✅ | `slice/mod.rs` |
| `[T]` | `as_array` | ✅ | `slice/mod.rs` |
| `[T]` | `as_mut_array` | ✅ | `slice/mod.rs` |
| `[T]` | `swap` | ✅ | `slice/mod.rs` |
| `[T]` | `swap_unchecked` | ⛔️ | nightly-only |
| `[T]` | `reverse` | ✅ | `slice/mod.rs` |
| `[T]` | `iter` | ✅ | `slice/mod.rs` |
| `[T]` | `iter_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `windows` | ✅ | `slice/mod.rs` |
| `[T]` | `chunks` | ✅ | `slice/mod.rs` |
| `[T]` | `chunks_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `chunks_exact` | ✅ | `slice/mod.rs` |
| `[T]` | `chunks_exact_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `as_chunks_unchecked` | ✅ | `slice/mod.rs` |
| `[T]` | `as_chunks` | ✅ | `slice/mod.rs` |
| `[T]` | `as_rchunks` | ✅ | `slice/mod.rs` |
| `[T]` | `as_chunks_unchecked_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `as_chunks_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `as_rchunks_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `array_windows` | ⚠️ | omitted |
| `[T]` | `rchunks` | ✅ | `slice/mod.rs` |
| `[T]` | `rchunks_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `rchunks_exact` | ✅ | `slice/mod.rs` |
| `[T]` | `rchunks_exact_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `chunk_by` | ✅ | `slice/mod.rs` |
| `[T]` | `chunk_by_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_at`| ✅ | `slice/mod.rs` |
| `[T]` | `split_at_mut`| ✅ | `slice/mod.rs` |
| `[T]` | `split_at_unchecked`| ✅ | `slice/mod.rs` |
| `[T]` | `split_at_mut_unchecked`| ✅ | `slice/mod.rs` |
| `[T]` | `split_at_checked`| ✅ | `slice/mod.rs` |
| `[T]` | `split_at_mut_checked`| ✅ | `slice/mod.rs` |
| `[T]` | `split` | ✅ | `slice/mod.rs` |
| `[T]` | `split_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_inclusive` | ✅ | `slice/mod.rs` |
| `[T]` | `split_inclusive_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `rsplit` | ✅ | `slice/mod.rs` |
| `[T]` | `rsplit_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `splitn` | ✅ | `slice/mod.rs` |
| `[T]` | `splitn_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `rsplitn` | ✅ | `slice/mod.rs` |
| `[T]` | `rsplitn_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_once` | ⛔️ | nightly-only |
| `[T]` | `rsplit_once` | ⛔️ | nightly-only |
| `[T]` | `contains` | ✅ | `slice/mod.rs` |
| `[T]` | `starts_with` | ✅ | `slice/mod.rs` |
| `[T]` | `ends_with` | ✅ | `slice/mod.rs` |
| `[T]` | `strip_prefix` | ⛔️ | `SlicePattern` |
| `[T]` | `strip_suffix` | ⛔️ | `SlicePattern` |
| `[T]` | `strip_circumfix` | ⛔️ | `SlicePattern` |
| `[T]` | `trim_prefix` | ⛔️ | `SlicePattern` |
| `[T]` | `trim_suffix` | ⛔️ | `SlicePattern` |
| `[T]` | `binary_search` | ✅ | `slice/mod.rs` |
| `[T]` | `binary_search_by` | ✅ | `slice/mod.rs` |
| `[T]` | `binary_search_by_key` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_unstable` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_unstable_by` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_unstable_by_key` | ✅ | `slice/mod.rs` |
| `[T]` | `partial_sort_unstable` | ⛔️ | nightly-only |
| `[T]` | `partial_sort_unstable_by` | ⛔️ | nightly-only |
| `[T]` | `partial_sort_unstable_by_key` | ⛔️ | nightly-only |
| `[T]` | `select_nth_unstable` | ✅ | `slice/mod.rs` |
| `[T]` | `select_nth_unstable_by` | ✅ | `slice/mod.rs` |
| `[T]` | `select_nth_unstable_by_key` | ✅ | `slice/mod.rs` |
| `[T]` | `partition_dedup` | ⛔️ | nightly-only |
| `[T]` | `partition_dedup_by` | ⛔️ | nightly-only |
| `[T]` | `partition_dedup_by_key` | ⛔️ | nightly-only |
| `[T]` | `rotate_left` | ✅ | `slice/mod.rs` |
| `[T]` | `rotate_right` | ✅ | `slice/mod.rs` |
| `[T]` | `shift_left` | ⛔️ | nightly-only |
| `[T]` | `shift_right` | ⛔️ | nightly-only |
| `[T]` | `fill` | ✅ | `slice/mod.rs` |
| `[T]` | `fill_with` | ✅ | `slice/mod.rs` |
| `[T]` | `clone_from_slice` | ✅ | `slice/mod.rs` |
| `[T]` | `copy_from_slice` | ✅ | `slice/mod.rs` |
| `[T]` | `copy_within` | ✅ | `slice/mod.rs` |
| `[T]` | `swap_with_slice` | ✅ | `slice/mod.rs` |
| `[T]` | `align_to` | ✅ | `slice/mod.rs` |
| `[T]` | `align_to_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `as_simd` | ⛔️ | nightly-only |
| `[T]` | `as_simd_mut` | ⛔️ | nightly-only |
| `[T]` | `is_sorted` | ✅ | `slice/mod.rs` |
| `[T]` | `is_sorted_by` | ✅ | `slice/mod.rs` |
| `[T]` | `is_sorted_by_key` | ✅ | `slice/mod.rs` |
| `[T]` | `partition_point` | ✅ | `slice/mod.rs` |
| `[T]` | `split_off` | ⛔️ | `OneSidedRange` |
| `[T]` | `split_off_mut` | ⛔️ | `OneSidedRange` |
| `[T]` | `split_off_first` | ✅ | `slice/mod.rs` |
| `[T]` | `split_off_first_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `split_off_last` | ✅ | `slice/mod.rs` |
| `[T]` | `split_off_last_mut` | ✅ | `slice/mod.rs` |
| `[T]` | `get_disjoint_unchecked_mut` | ⛔️ | `GetDisjointMutIndex` |
| `[T]` | `get_disjoint_mut` | ⛔️ | `GetDisjointMutIndex` |
| `[T]` | `element_offset` | ✅ | `slice/mod.rs` |
| `[T]` | `subslice_range` | ✅ | `slice/mod.rs` |
| `[T]` | `as_slice` | ⛔️ | nightly-only |
| `[T]` | `as_mut_slice` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `align_to_uninit_mut` | ⛔️ | nightly-only |
| `[[T; N]]` | `as_flattened` | ⛔️ | foreign type |
| `[[T; N]]` | `as_flattened_mut` | ⛔️ | foreign type |
| `[f32]` | `sort_floats` | ⛔️ | nightly-only |
| `[f64]` | `sort_floats` | ⛔️ | nightly-only |
| `[u8]` | `utf8_chunks` | ✅ | `slice/mod.rs` |
| `[T]` | `sort` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_by` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_by_key` | ✅ | `slice/mod.rs` |
| `[T]` | `sort_by_cached_key` | ✅ | `slice/mod.rs` |
| `[T]` | `to_vec` | ✅ | `slice/mod.rs` |
| `[T]` | `to_vec_in` | ✅ | `slice/mod.rs` |
| `[T]` | `into_vec` | ✅ | `slice/mod.rs` |
| `[T]` | `repeat` | ✅ | `slice/mod.rs` |
| `[T]` | `concat` | ✅ | `slice/mod.rs` |
| `[T]` | `join` | ✅ | `slice/mod.rs` |
| `[T]` | `connect` | ⛔️ | deprecated |
| `[u8]` | `to_ascii_uppercase` | ✅ | `slice/mod.rs` |
| `[u8]` | `to_ascii_lowercase` | ✅ | `slice/mod.rs` |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Box<[T], A>` | `Clone` | ✅ | `slice/boxed.rs` |
| `[T]` | `CloneToUninit` | ⛔️ | nightly-only |
| `[T]` | `ConstParamTy_` | ⛔️ | nightly-only |
| `[T]` | `Eq` | ✅ | `slice/mod.rs` |
| `[T]` | `PartialEq<[U]>` | ✅ | `slice/mod.rs` |
| `&[T]` | `PartialEq<[U]>` | | |
| `&mut [T]` | `PartialEq<[U]>` | | |
| `[T]` | `PartialEq<[U; N]>` | | |
| `&[T]` | `PartialEq<[U; N]>` | | |
| `[T; N]` | `PartialEq<&[U]>` | | |
| `&mut [T]` | `PartialEq<[U; N]>` | | |
| `[T; N]` | `PartialEq<&mut [U]>` | | |
| `&[T]` | `PartialEq<Cow<'_, [U]>>` | | |
| `Cow<'_, [T]>` | `PartialEq<&[U]>` | | |
| `&mut [T]` | `PartialEq<Cow<'_, [U]>>` | | |
| `Cow<'_, [T]>` | `PartialEq<&mut [U]>` | | |
| `[T]` | `PartialEq<Vec<U, A>>` | | |
| `&[T]` | `PartialEq<Vec<U, A>>` | | |
| `&mut [T]` | `PartialEq<Vec<U, A>>` | | |
| `Vec<T, A>` | `PartialEq<&[U]>` | | |
| `Vec<T, A>` | `PartialEq<&mut [U]>` | | |
| `VecDeque<T, A>` | `PartialEq<&[U]>` | ⚠️ | omitted |
| `VecDeque<T, A>` | `PartialEq<&mut [U]>` | ⚠️ | omitted |
| `ByteStr` | `PartialEq<&[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<&[u8]>` | ⛔️ | nightly-only |
| `ByteStr` | `PartialEq<[u8]>` | ⛔️ | nightly-only |
| `[u8]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `&[u8]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<[u8]>` | ⛔️ | nightly-only |
| `[u8]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `&[u8]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `[T]` | `StructuralPartialEq` | ⛔️ | nightly-only |
| `[T]` | `Ord` | ✅ | `slice/mod.rs` |
| `[T]` | `PartialOrd` | ✅ | `slice/mod.rs` |
| `[T]` | `Hash` | ✅ | `slice/mod.rs` |
| `&[T]` | `Default` | ✅ | `slice/mod.rs` |
| `&mut [T]` | `Default` | ✅ | `slice/mod.rs` |
| `Box<[T]>` | `Default` | ✅ | `slice/boxed.rs` |
| `[T]` | `Debug` | ✅ | `slice/mod.rs` |
| `[T]` | `AsRef<[T]>` | ✅ | `slice/mod.rs` |
| `[T; N]` | `AsRef<[T]>` | ✅ | `array/mod.rs` |
| `Vec<T, A>` | `AsRef<[T]>` | ✅ | `vec.rs` |
| `MaybeUninit<[T; N]>` | `AsRef<[MaybeUninit<T>]>` | | |
| `Cell<[T]>` | `AsRef<[Cell<T>]>` | | |
| `Cell<[T; N]>` | `AsRef<[Cell<T>]>` | | |
| `Drain<'_, T, A>` | `AsRef<[T]>` | | |
| `IntoIter<T, A>` | `AsRef<[T]>` | | |
| `Iter<'_, T>` | `AsRef<[T]>` | | |
| `IterMut<'_, T>` | `AsRef<[T]>` | | |
| `Simd<T, N>` | `AsRef<[T]>` | ⛔️ | nightly-only |
| `ByteStr` | `AsRef<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `AsRef<[u8]>` | ⛔️ | nightly-only |
| `Drain<'a>` | `AsRef<[u8]>` | | |
| `String` | `AsRef<[u8]>` | | |
| `str` | `AsRef<[u8]>` | | |
| `[T]` | `AsMut<[T]>` | ✅ | `slice/mod.rs` |
| `[T; N]` | `AsMut<[T]>` | ✅ | `array/mod.rs` |
| `Vec<T, A>` | `AsMut<[T]>` | ✅ | `vec.rs` |
| `MaybeUninit<[T; N]>` | `AsMut<[MaybeUninit<T>]>` | | |
| `Simd<T, N>` | `AsMut<[T]>` | ⛔️ | nightly-only |
| `ByteStr` | `AsMut<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `AsMut<[u8]>` | ⛔️ | nightly-only |
| `[T; N]` | `Borrow<[T]>` | ✅ | `array/mod.rs` |
| `Vec<T, A>` | `Borrow<[T]>` | ✅ | `vec.rs` |
| `ByteStr` | `Borrow<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `Borrow<[u8]>` | ⛔️ | nightly-only |
| `[T; N]` | `BorrowMut<[T]>` | ✅ | `array/mod.rs` |
| `Vec<T, A>` | `BorrowMut<[T]>` | ✅ | `vec.rs` |
| `ByteStr` | `BorrowMut<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `BorrowMut<[u8]>` | ⛔️ | nightly-only |
| `Box<[T]>` | `From<[T; N]>` | ✅ | `array/boxed.rs` |
| `Box<[T]>` | `From<&[T]>` | | |
| `Box<[T]>` | `From<&mut [T]>` | | |
| `Box<[T]>` | `From<Cow<'_, [T]>>` | | |
| `Box<[T], A>` | `From<Vec<T, A>>` | | |
| `Rc<[T]>` | `From<&[T]>` | | |
| `Rc<[T]>` | `From<&mut [T]>` | | |
| `Arc<[T]>` | `From<&[T]>` | | |
| `Arc<[T]>` | `From<&mut [T]>` | | |
| `Cow<'_, [T]>` | `From<&[T]>` | ✅ | `slice/mod.rs` |
| `Vec<T>` | `From<&[T]>` | | |
| `Vec<T>` | `From<&mut [T]>` | | |
| `Vec<T, A>` | `From<Box<[T], A>>` | | |
| `Box<[u8], A>` | `From<Box<str, A>>` | | |
| `BorrowedBuf<'_, T>` | `From<&mut [MaybeUninit<T>]>` | | |
| `BorrowedBuf<'_, T>` | `From<&mut [T]>` | | |
| `Box<[u8]>` | `From<Box<ByteStr>>` | ⛔️ | nightly-only |
| `Box<ByteStr>` | `From<Box<[u8]>>` | ⛔️ | nightly-only |
| `&[T; N]` | `TryFrom<&[T]>` | | |
| `[T; N]` | `TryFrom<&[T]>` | | |
| `[T; N]` | `TryFrom<&mut [T]>` | | |
| `&mut [T; N]` | `TryFrom<&mut [T]>` | | |
| `Box<[T; N], A>` | `TryFrom<Box<[T], A>>` | | |
| `Simd<T, N>` | `TryFrom<&[T]>` | | |
| `Simd<T, N>` | `TryFrom<&mut [T]>` | | |
| `[T]` | `!Iterator` | ⛔️ | nightly-only |
| `Box<[T]>` | `!Iterator` | ⛔️ | nightly-only |
| `&Box<[T]>` | `!Iterator` | ⛔️ | nightly-only |
| `&mut Box<[T]>` | `!Iterator` | ⛔️ | nightly-only |
| `&[T]` | `IntoIterator` | ✅ | `slice/mod.rs` |
| `&mut [T]` | `IntoIterator` | ✅ | `slice/mod.rs` |
| `Box<[T], A>` | `IntoIterator` | | |
| `&Box<[T], A>` | `IntoIterator` | | |
| `&mut Box<[T], A>` | `IntoIterator` | | |
| `Box<[T]>` | `FromIterator<T>` | | |
| `ByteString` | `FromIterator<&[u8]>` | ⛔️ | nightly-only |
| `[T]` | `Index<I>` | ✅ | `slice/mod.rs` |
| `[T]` | `IndexMut<I>` | ✅ | `slice/mod.rs` |
| `[T]` | `ToOwned` | | |
| `&[u8]` | `Read` | ✅ | `slice/mod.rs` |
| `&[u8]` | `BufRead` | ✅ | `slice/mod.rs` |
| `&mut [u8]` | `Write` | ✅ | `slice/mod.rs` |
| `&[SocketAddr]` | `ToSocketAddrs` | | |
| `[u8]` | `AsciiExt` | ⛔️ | deprecated |
| `&'b [char]` | `Pattern` | ⛔️ | nightly-only |
| `[S]` | `Join<&OsStr>` | ⛔️ | nightly-only |
| `[V]` | `Join<&T>` | ⛔️ | nightly-only |
| `[V]` | `Join<&[T]>` | ⛔️ | nightly-only |
| `[S]` | `Join<&str>` | ⛔️ | nightly-only |
| `[V]` | `Concat<T>` | ⛔️ | nightly-only |
| `[S]` | `Concat<str>` | ⛔️ | nightly-only |
| `(Bound<usize>, Bound<usize>)` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `usize` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `ops::Range<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `range::Range<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `ops::RangeFrom<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `range::RangeFrom<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `ops::RangeInclusive<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `range::RangeInclusive<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `RangeTo<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `ops::RangeToInclusive<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `range::RangeToInclusive<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `RangeFull` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<usize>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<ops::Range<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<range::Range<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<ops::RangeFrom<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<range::RangeFrom<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<ops::RangeInclusive<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<range::RangeInclusive<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<RangeTo<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<ops::RangeToInclusive<usize>>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<range::RangeToInclusive<usize>>`| `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Clamp<RangeFull>` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |
| `Last` | `SliceIndex<[T]>` | ⛔️ | impl in stdlib only |

## API parity with `[T; N]`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `[T; N]` | `map` | ✅ | `array/mod.rs` |
| `[T; N]` | `as_slice` | ✅ | `array/mod.rs` |
| `[T; N]` | `as_mut_slice` | ✅ | `array/mod.rs` |
| `[T; N]` | `each_ref` | ✅ | `array/mod.rs` |
| `[T; N]` | `each_mut` | ✅ | `array/mod.rs` |
| `[T; N]` | `try_map` | ⛔️ | nightly-only |
| `[T; N]` | `transpose` | ⛔️ | nightly-only |
| `[T; N]` | `rsplit_array_mut` | ⛔️ | nightly-only |
| `[T; N]` | `rsplit_array_ref` | ⛔️ | nightly-only |
| `[T; N]` | `split_array_mut` | ⛔️ | nightly-only |
| `[T; N]` | `split_array_ref` | ⛔️ | nightly-only |
| `[u8; N]` | `as_ascii` | ⛔️ | nightly-only |
| `[u8; N]` | `as_ascii_unchecked` | ⛔️ | nightly-only |
| `[MaybeUninit<T>; N]` | `transpose` | ⛔️ | nightly-only |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `[T; N]` | `Copy` | ✅ | `array/mod.rs` |
| `[T; N]` | `Clone` | ✅ | `array/mod.rs` |
| `[T; N]` | `CloneFromCell` | ⛔️ | nightly-only |
| `[T; N]` | `ConstParamTy_` | ⛔️ | nightly-only |
| `[T; N]` | `Eq` | ✅ | `array/mod.rs` |
| `[T; N]` | `PartialEq<[U; N]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `PartialEq<[U]>` | ✅ | `array/mod.rs` |
| `[T]` | `PartialEq<[U; N]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `PartialEq<&[U]>` | ✅ | `array/mod.rs` |
| `&[T]` | `PartialEq<[U; N]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `PartialEq<&mut [U]>` | ✅ | `array/mod.rs` |
| `&mut [T]` | `PartialEq<[U; N]>` | ✅ | `array/mod.rs` |
| `Vec<T, A>` | `PartialEq<[U; N]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<&[U; N]>` | ✅ | `vec.rs` |
| `VecDeque<T, A>` | `PartialEq<[U; N]>` | ⚠️ | omitted |
| `VecDeque<T, A>` | `PartialEq<&[U; N]>` | ⚠️ | omitted |
| `VecDeque<T, A>` | `PartialEq<&mut [U; N]>` | ⚠️ | omitted |
| `ByteStr` | `PartialEq<[u8; N]>` | ⛔️ | nightly-only |
| `[u8; N]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteStr` | `PartialEq<&[u8; N]>` | ⛔️ | nightly-only |
| `&[u8; N]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<[u8; N]>` | ⛔️ | nightly-only |
| `[u8; N]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<&[u8; N]>` | ⛔️ | nightly-only |
| `&[u8; N]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `[u8; N]` | `StructuralPartialEq` | ⛔️ | nightly-only |
| `[T; N]` | `Ord` | ✅ | `array/mod.rs` |
| `[T; N]` | `PartialOrd` | ✅ | `array/mod.rs` |
| `[T; N]` | `Hash` | ✅ | `array/mod.rs` |
| `[T; N]` | `Default` | ✅ | `array/mod.rs` |
| `[T; N]` | `Debug` | ✅ | `array/mod.rs` |
| `[T; N]` | `AsRef<Self>` | ✅ | `array/mod.rs` |
| `[T; N]` | `AsRef<[T]>` | ✅ | `array/mod.rs` |
| `Cell<[T; N]>` | `AsRef<[Cell<T>; N]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `AsMut<Self>` | ✅ | `array/mod.rs` |
| `[T; N]` | `AsMut<[T]>` | ✅ | `array/mod.rs` |
| `MaybeUninit<[T; N]>` | `AsRef<[MaybeUninit<T>; N]>` | ✅ | `array/mod.rs` |
| `MaybeUninit<[T; N]>` | `AsMut<[MaybeUninit<T>; N]>` | ✅ | `array/mod.rs` |
| `Simd<T, N>` | `AsRef<[T; N]>` | ⛔️ | nightly-only |
| `Simd<T, N>` | `AsMut<[T; N]>` | ⛔️ | nightly-only |
| `[T; N]` | `Borrow<[T]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `BorrowMut<[T]>` | ✅ | `array/mod.rs` |
| `MaybeUninit<[MaybeUninit<T>; N]>` | `From<[T; N]>` | ✅ | `array/mod.rs` |
| `MaybeUninit<[T; N]>` | `From<[MaybeUninit<T>; N]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `From<(T₁, T₂, …, Tₙ)>` | ✅ | `array/mod.rs` |
| `(T₁, T₂, …, Tₙ)` | `From<[T; N]>` | ✅ | `array/mod.rs` |
| `Box<[T]>` | `From<[T; N]>` | ✅ | `array/boxed.rs` |
| `Rc<[T]>` | `From<[T; N]>` | | |
| `Arc<[T]>` | `From<[T; N]>` | | |
| `Cow<'a, [T]>` | `From<&[T; N]>` | | |
| `Vec<T>` | `From<[T; N]>` | | |
| `Vec<T>` | `From<&[T; N]>` | | |
| `Vec<T>` | `From<&mut [T; N]>` | | |
| `VecDeque<T>` | `From<[T; N]>` | ⚠️ | omitted |
| `BTreeSet<T>` | `From<[T; N]>` | ⚠️ | omitted |
| `BTreeMap<K, V>` | `From<[(K, V); N]>` | ⚠️ | omitted |
| `HashMap<K, V>` | `From<[(K, V); N]>` | ⚠️ | omitted |
| `HashSet<T>` | `From<[T; N]>` | ⚠️ | omitted |
| `BinaryHeap<T>` | `From<[T; N]>` | ⚠️ | omitted |
| `LinkedList<T>` | `From<[T; N]>` | ⚠️ | omitted |
| `[T; N]` | `From<Simd<T, N>>` | ⛔️ | nightly-only |
| `Simd<T, N>` | `From<[T; N]>` | ⛔️ | nightly-only |
| `[bool; N]` | `From<Mask<T, N>>` | ⛔️ | nightly-only |
| `IpAddr` | `From<[u8; 4]>` | | |
| `Ipv4Addr` | `From<[u8; 4]>` | | |
| `IpAddr` | `From<[u8; 16]>` | | |
| `Ipv6Addr` | `From<[u8; 16]>` | | |
| `IpAddr` | `From<[u16; 8]>` | | |
| `Ipv6Addr` | `From<[u16; 8]>` | | |
| `[T; N]` | `TryFrom<&[T]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `TryFrom<&mut [T]>` | ✅ | `array/mod.rs` |
| `&[T; N]` | `TryFrom<&[T]>` | ✅ | `array/mod.rs` |
| `&mut [T; N]` | `TryFrom<&mut [T]>` | ✅ | `array/mod.rs` |
| `Box<[T; N], A>` | `TryFrom<Box<T>, A>` | | |
| `[T; N]` | `TryFrom<Vec<T, A>>` | ✅ | `vec.rs` |
| `Box<[T; N], A>` | `TryFrom<Vec<T, A>>` | ✅ | `vec.rs` |
| `[T; N]` | `!Iterator` | ⛔️ | nightly-only |
| `Box<[T; N]>` | `!Iterator` | ⛔️ | nightly-only |
| `&Box<[T; N]>` | `!Iterator` | ⛔️ | nightly-only |
| `&mut Box<[T; N]>` | `!Iterator` | ⛔️ | nightly-only |
| `[T; N]` | `IntoIterator` | ✅ | `array/mod.rs` |
| `&[T; N]` | `IntoIterator` | ✅ | `array/mod.rs` |
| `&mut [T; N]` | `IntoIterator` | ✅ | `array/mod.rs` |
| `Box<[T; N]>` | `IntoIterator` | ✅ | `array/boxed.rs`
| `&Box<[T; N]>` | `IntoIterator` | ✅ | `array/boxed.rs`
| `&mut Box<[T; N]>` | `IntoIterator` | ✅ | `array/boxed.rs`
| `[T; N]` | `Index<I>` | ✅ | `array/mod.rs` |
| `[T; N]` | `IndexMut<I>` | ✅ | `array/mod.rs` |
| `[char; N]` | `Pattern` | ⛔️ | nightly-only |
| `&[char; N]` | `Pattern` | ⛔️ | nightly-only |

## API parity with `Vec<T>`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Vec<T>` | `new` | ✅ | `vec.rs` |
| `Vec<T>` | `with_capacity` | ✅ | `vec.rs` |
| `Vec<T>` | `try_with_capacity` | ⛔️ | nightly-only |
| `Vec<T>` | `from_raw_parts` | ✅ | `vec.rs` |
| `Vec<T>` | `from_parts` | ✅ | `vec.rs` |
| `Vec<T>` | `from_fn` | ✅ | `vec.rs` |
| `Vec<T>` | `into_raw_parts` | ✅ | `vec.rs` |
| `Vec<T>` | `into_parts` | ✅ | `vec.rs` |
| `Vec<T>` | `const_make_global` | ⛔️ | nightly-only |
| `Vec<T, A>` | `with_capacity_in` | ✅ | `vec.rs` |
| `Vec<T, A>` | `push` | ✅ | `vec.rs` |
| `Vec<T, A>` | `push_mut` | ✅ | `vec.rs` |
| `Vec<T, A>` | `new_in` | ✅ | `vec.rs` |
| `Vec<T, A>` | `try_with_capacity_in` | ⛔️ | nightly-only |
| `Vec<T, A>` | `from_raw_parts_in` | ✅ | `vec.rs` |
| `Vec<T, A>` | `from_parts_in` | ✅ | `vec.rs` |
| `Vec<T, A>` | `into_raw_parts_with_allocator` | ✅ | `vec.rs` |
| `Vec<T, A>` | `into_parts_with_allocator` | ✅ | `vec.rs` |
| `Vec<T, A>` | `capacity` | ✅ | `vec.rs` |
| `Vec<T, A>` | `reserve` | ✅ | `vec.rs` |
| `Vec<T, A>` | `reserve_exact` | ✅ | `vec.rs` |
| `Vec<T, A>` | `try_reserve` | ✅ | `vec.rs` |
| `Vec<T, A>` | `try_reserve_exact` | ✅ | `vec.rs` |
| `Vec<T, A>` | `shrink_to_fit` | ✅ | `vec.rs` |
| `Vec<T, A>` | `shrink_to` | ✅ | `vec.rs` |
| `Vec<T, A>` | `try_shrink_to_fit` | ⛔️ | nightly-only |
| `Vec<T, A>` | `try_shrink_to` | ⛔️ | nightly-only |
| `Vec<T, A>` | `into_boxed_slice` | ✅ | `vec.rs` |
| `Vec<T, A>` | `into_array` | ⛔️ | nightly-only |
| `Vec<T, A>` | `truncate` | ✅ | `vec.rs` |
| `Vec<T, A>` | `as_slice` | ✅ | `vec.rs` |
| `Vec<T, A>` | `as_mut_slice` | ✅ | `vec.rs` |
| `Vec<T, A>` | `as_ptr` | ✅ | `vec.rs` |
| `Vec<T, A>` | `as_mut_ptr` | ✅ | `vec.rs` |
| `Vec<T, A>` | `as_non_null` | ⛔️ | nightly-only |
| `Vec<T, A>` | `allocator` | ✅ | `vec.rs` |
| `Vec<T, A>` | `set_len` | ✅ | `vec.rs` |
| `Vec<T, A>` | `swap_remove` | ✅ | `vec.rs` |
| `Vec<T, A>` | `insert` | ✅ | `vec.rs` |
| `Vec<T, A>` | `insert_mut` | ✅ | `vec.rs` |
| `Vec<T, A>` | `remove` | ✅ | `vec.rs` |
| `Vec<T, A>` | `try_remove` | ⛔️ | nightly-only |
| `Vec<T, A>` | `retain` | ✅ | `vec.rs` |
| `Vec<T, A>` | `retain_mut` | ✅ | `vec.rs` |
| `Vec<T, A>` | `dedup_by_key` | ✅ | `vec.rs` |
| `Vec<T, A>` | `dedup_by` | ✅ | `vec.rs` |
| `Vec<T, A>` | `push_within_capacity` | ⛔️ | nightly-only |
| `Vec<T, A>` | `pop` | ✅ | `vec.rs` |
| `Vec<T, A>` | `pop_if` | ✅ | `vec.rs` |
| `Vec<T, A>` | `peek_mut` | ⛔️ | nightly-only |
| `Vec<T, A>` | `append` | ✅ | `vec.rs` |
| `Vec<T, A>` | `drain` | ⚠️/⛔️ | `AllocatorNightly` |
| `Vec<T>` | `drain` | ✅ | `vec.rs` |
| `Vec<T, A>` | `clear` | ✅ | `vec.rs` |
| `Vec<T, A>` | `len` | ✅ | `vec.rs` |
| `Vec<T, A>` | `is_empty` | ✅ | `vec.rs` |
| `Vec<T, A>` | `split_off` | ✅ | `vec.rs` |
| `Vec<T, A>` | `resize_with` | ✅ | `vec.rs` |
| `Vec<T, A>` | `leak` | ✅ | `vec.rs` |
| `Vec<T, A>` | `spare_capacity_mut` | ✅ | `vec.rs` |
| `Vec<T, A>` | `split_at_spare_mut` | ⛔️ | nightly-only |
| `Vec<T, A>` | `into_chunks` | ⛔️ | nightly-only |
| `Vec<T, A>` | `recycle` | ⛔️ | nightly-only |
| `Vec<T, A>` | `resize` | ✅ | `vec.rs` |
| `Vec<T, A>` | `extend_from_slice` | ✅ | `vec.rs` |
| `Vec<T, A>` | `extend_from_within` | ✅ | `vec.rs` |
| `Vec<[T; N], A>` | `into_flattened` | ✅ | `vec.rs` |
| `Vec<T, A>` | `dedup` | ✅ | `vec.rs` |
| `Vec<T, A>` | `splice` | ⚠️/⛔️ | `AllocatorNightly` |
| `Vec<T>` | `splice` | ✅ | `vec.rs` |
| `Vec<T, A>` | `extract_if` | ⚠️/⛔️ | `AllocatorNightly` |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Vec<T, A>` | `Clone` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Eq` | ✅ | `vec.rs` |
| `Vec<T, A1>` | `PartialEq<Vec<U, A2>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<[U]>` | ✅ | `vec.rs` |
| `[T]` | `PartialEq<Vec<U, A>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<[U; N]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<&[U; N]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<&[U]>` | ✅ | `vec.rs` |
| `&[T]` | `PartialEq<Vec<U, A>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `PartialEq<&mut [U]>` | ✅ | `vec.rs` |
| `&mut [T]` | `PartialEq<Vec<U, A>>` | ✅ | `vec.rs` |
| `Cow<'_, [T]>`| `PartialEq<Vec<U, A>>` | | |
| `Vec<T, A>` | `PartialEq<Cow<'_, [U]>>` | | |
| `VecDeque<T, A>` | `PartialEq<Vec<U, A>>` | ⚠️ | omitted |
| `Vec<u8>` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteStr` | `PartialEq<Vec<u8>>` | ⛔️ | nightly-only |
| `Vec<u8>` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<Vec<u8>>` | ⛔️ | nightly-only |
| `Vec<T, A>` | `Ord` | ✅ | `vec.rs` |
| `Vec<T, A1>` | `PartialOrd<Vec<T, A2>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Hash` | ✅ | `vec.rs` |
| `Vec<T>` | `Default` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Drop` | ✅/⚠️ | implicit |
| `Vec<T, A>` | `Debug` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Deref` | ✅ | `vec.rs` |
| `Vec<T, A>` | `DerefMut` | ✅ | `vec.rs` |
| `Vec<T, A>` | `DerefPure` | ⛔️ | nightly-only |
| `Vec<T, A>` | `AsRef<Vec<T, A>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `AsRef<[T]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `AsMut<Vec<T, A>>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `AsMut<[T]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Borrow<[T]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `BorrowMut<[T]>` | ✅ | `vec.rs` |
| `Vec<T>` | `From<[T; N]>` | ✅ | `vec.rs` |
| `Vec<T>` | `From<&[T; N]>` | ✅ | `vec.rs` |
| `Vec<T>` | `From<&mut [T; N]>` | ✅ | `vec.rs` |
| `Vec<T>` | `From<&[T]>` | ✅ | `vec.rs` |
| `Vec<T>` | `From<&mut [T]>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `From<Box<[T], A>>` | | |
| `Box<[T], A>` | `From<Vec<T, A>>` | | |
| `Vec<T>` | `From<Cow<'a, [T]>>` | ✅ | `vec.rs` |
| `Cow<'_, [T]>` | `From<Vec<T>>` | ✅ | `vec.rs` |
| `Cow<'_, [T]>` | `From<&Vec<T>>` | ✅ | `vec.rs` |
| `Rc<[T], A>` | `From<Vec<T, A>>` | | |
| `Arc<[T], A>` | `From<Vec<T, A>>` | | |
| `Vec<T, A>` | `From<VecDeque<T, A>>` | ⚠️ | omitted |
| `VecDeque<T, A>` | `From<Vec<T, A>>` | ⚠️ | omitted |
| `Vec<T, A>` | `From<BinaryHeap<T, A>>` | ⚠️ | omitted |
| `BinaryHeap<T, A>` | `From<Vec<T, A>>` | ⚠️ | omitted |
| `CString` | `From<Vec<NonZero<u8>>>` | | |
| `Vec<u8>` | `From<&str>` | ✅ | `vec.rs` |
| `Vec<u8>` | `From<String>` | ✅ | `vec.rs` |
| `Vec<u8>` | `From<CString>` | ✅ | `vec.rs` |
| `Vec<u8>` | `From<ByteString>` | ⛔️ | nightly-only |
| `[T; N]` | `TryFrom<Vec<T, A>>` | ✅ | `vec.rs` |
| `Box<[T; N], A>` | `TryFrom<Vec<T, A>>` | ✅ | `vec.rs` |
| `String` | `TryFrom<Vec<u8>>` | | |
| Vec<T, A>| `IntoIterator` | ✅ | `vec.rs` |
| &Vec<T, A> | `IntoIterator` | ✅ | `vec.rs` |
| &mut Vec<T, A> | `IntoIterator`| ✅ | `vec.rs` |
| `Vec<T>` | `FromIterator<T>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Index<I>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `IndexMut<I>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Extend<T>` | ✅ | `vec.rs` |
| `Vec<T, A>` | `Extend<&T>` | ✅ | `vec.rs` |
| `Vec<u8, A>` | `Write` | ✅ | `vec.rs` |
