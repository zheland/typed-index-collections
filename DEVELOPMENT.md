# Development

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
| `[T]` | `PartialEq<[U; N]>` | ⚠️ | missing |
| `[T; N]` | `PartialEq<&[U]>` | ✅ | `array/mod.rs` |
| `&[T]` | `PartialEq<[U; N]>` | ⚠️ | missing |
| `[T; N]` | `PartialEq<&mut [U]>` | ✅ | `array/mod.rs` |
| `&mut [T]` | `PartialEq<[U; N]>` | ⚠️ | missing |
| `Vec<T, A>` | `PartialEq<[U; N]>` | ⚠️ | missing |
| `Vec<T, A>` | `PartialEq<&[U; N]>` | ⚠️ | missing |
| `VecDeque<T, A>` | `PartialEq<[U; N]>` | ⚠️ | missing |
| `VecDeque<T, A>` | `PartialEq<&[U; N]>` | ⚠️ | missing |
| `VecDeque<T, A>` | `PartialEq<&mut [U; N]>` | ⚠️ | missing |
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
| `Box<[T]>` | `From<[T; N]>` | ⚠️ | missing |
| `Rc<[T]>` | `From<[T; N]>` | ⚠️ | missing |
| `Arc<[T]>` | `From<[T; N]>` | ⚠️ | missing |
| `Cow<'a, [T]>` | `From<&[T; N]>` | ⚠️ | missing |
| `Vec<T>` | `From<[T; N]>` | ⚠️ | missing |
| `Vec<T>` | `From<&[T; N]>` | ⚠️ | missing |
| `Vec<T>` | `From<&mut [T; N]>` | ⚠️ | missing |
| `VecDeque<T>` | `From<[T; N]>` | ⚠️ | missing |
| `BTreeSet<T>` | `From<[T; N]>` | ⚠️ | missing |
| `BTreeMap<K, V>` | `From<[(K, V); N]>` | ⚠️ | missing |
| `HashMap<K, V>` | `From<[(K, V); N]>` | ⚠️ | missing |
| `HashSet<T>` | `From<[T; N]>` | ⚠️ | missing |
| `BinaryHeap<T>` | `From<[T; N]>` | ⚠️ | missing |
| `LinkedList<T>` | `From<[T; N]>` | ⚠️ | missing |
| `[T; N]` | `From<Simd<T, N>>` | ⛔️ | nightly-only |
| `Simd<T, N>` | `From<[T; N]>` | ⛔️ | nightly-only |
| `[bool; N]` | `From<Mask<T, N>>` | ⛔️ | nightly-only |
| `IpAddr` | `From<[u8; 4]>` | ⚠️ | missing |
| `Ipv4Addr` | `From<[u8; 4]>` | ⚠️ | missing |
| `IpAddr` | `From<[u8; 16]>` | ⚠️ | missing |
| `Ipv6Addr` | `From<[u8; 16]>` | ⚠️ | missing |
| `IpAddr` | `From<[u16; 8]>` | ⚠️ | missing |
| `Ipv6Addr` | `From<[u16; 8]>` | ⚠️ | missing |
| `[T; N]` | `TryFrom<&[T]>` | ✅ | `array/mod.rs` |
| `[T; N]` | `TryFrom<&mut [T]>` | ✅ | `array/mod.rs` |
| `&[T; N]` | `TryFrom<&[T]>` | ✅ | `array/mod.rs` |
| `&mut [T; N]` | `TryFrom<&mut [T]>` | ✅ | `array/mod.rs` |
| `Box<[T; N], A>` | `TryFrom<Box<T>, A>` | ⚠️ | missing |
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

## API parity with `[T]`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Box<[T]>` | `new_uninit_slice` | | |
| `Box<[T]>` | `new_zeroed_slice` | | |
| `Box<[T]>` | `try_new_uninit_slice` | ⛔️ | nightly-only |
| `Box<[T]>` | `try_new_zeroed_slice` | ⛔️ | nightly-only |
| `Box<[T], A>` | `new_uninit_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `new_zeroed_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `try_new_uninit_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `try_new_zeroed_slice_in` | ⛔️ | nightly-only |
| `Box<[T], A>` | `into_array` | ⛔️ | nightly-only |
| `Box<[MaybeUninit<T>], A>` | `assume_init` | | |
| `[MaybeUninit<T>]` | `write_copy_of_slice` | | |
| `[MaybeUninit<T>]` | `write_clone_of_slice` | | |
| `[MaybeUninit<T>]` | `write_filled` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_with` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_default` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `write_iter` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `as_bytes` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `as_bytes_mut` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `assume_init_drop` | | |
| `[MaybeUninit<T>]` | `assume_init_ref` | | |
| `[MaybeUninit<T>]` | `assume_init_mut` | | |
| `[AsciiChar]` | `as_str` | ⛔️ | nightly-only |
| `[AsciiChar]` | `as_bytes` | ⛔️ | nightly-only |
| `[u8]` | `is_ascii` | | |
| `[u8]` | `as_ascii` | | |
| `[u8]` | `as_ascii_unchecked` | | |
| `[u8]` | `eq_ignore_ascii_case` | | |
| `[u8]` | `make_ascii_uppercase` | | |
| `[u8]` | `make_ascii_lowercase` | | |
| `[u8]` | `escape_ascii` | | |
| `[u8]` | `trim_ascii_start` | | |
| `[u8]` | `trim_ascii_end` | | |
| `[u8]` | `trim_ascii` | | |
| `[u8]` | `split_ascii_whitespace` | | |
| `[T]` | `len` | | |
| `[T]` | `is_empty` | | |
| `[T]` | `first` | | |
| `[T]` | `first_mut` | | |
| `[T]` | `split_first` | | |
| `[T]` | `split_first_mut` | | |
| `[T]` | `split_last` | | |
| `[T]` | `split_last_mut` | | |
| `[T]` | `last` | | |
| `[T]` | `last_mut` | | |
| `[T]` | `first_chunk` | | |
| `[T]` | `first_chunk_mut` | | |
| `[T]` | `split_first_chunk` | | |
| `[T]` | `split_first_chunk_mut` | | |
| `[T]` | `split_last_chunk` | | |
| `[T]` | `split_last_chunk_mut` | | |
| `[T]` | `last_chunk` | | |
| `[T]` | `last_chunk_mut` | | |
| `[T]` | `get` | | |
| `[T]` | `get_mut` | | |
| `[T]` | `get_unchecked` | | |
| `[T]` | `get_unchecked_mut` | | |
| `[T]` | `as_ptr` | | |
| `[T]` | `as_mut_ptr` | | |
| `[T]` | `as_ptr_range` | | |
| `[T]` | `as_mut_ptr_range` | | |
| `[T]` | `as_array` | | |
| `[T]` | `as_mut_array` | | |
| `[T]` | `swap` | | |
| `[T]` | `swap_unchecked` | ⛔️ | nightly-only |
| `[T]` | `reverse` | | |
| `[T]` | `iter` | | |
| `[T]` | `iter_mut` | | |
| `[T]` | `windows` | | |
| `[T]` | `chunks` | | |
| `[T]` | `chunks_mut` | | |
| `[T]` | `chunks_exact` | | |
| `[T]` | `chunks_exact_mut` | | |
| `[T]` | `as_chunks_unchecked` | | |
| `[T]` | `as_chunks` | | |
| `[T]` | `as_rchunks` | | |
| `[T]` | `as_chunks_unchecked_mut` | | |
| `[T]` | `as_chunks_mut` | | |
| `[T]` | `as_rchunks_mut` | | |
| `[T]` | `array_windows` | | |
| `[T]` | `rchunks` | | |
| `[T]` | `rchunks_mut` | | |
| `[T]` | `rchunks_exact` | | |
| `[T]` | `rchunks_exact_mut` | | |
| `[T]` | `chunk_by` | | |
| `[T]` | `chunk_by_mut` | | |
| `[T]` | `split_at` | | |
| `[T]` | `split_at_mut` | | |
| `[T]` | `split_at_unchecked` | | |
| `[T]` | `split_at_mut_unchecked` | | |
| `[T]` | `split_at_checked` | | |
| `[T]` | `split_at_mut_checked` | | |
| `[T]` | `split` | | |
| `[T]` | `split_mut` | | |
| `[T]` | `split_inclusive` | | |
| `[T]` | `split_inclusive_mut` | | |
| `[T]` | `rsplit` | | |
| `[T]` | `rsplit_mut` | | |
| `[T]` | `splitn` | | |
| `[T]` | `splitn_mut` | | |
| `[T]` | `rsplitn` | | |
| `[T]` | `rsplitn_mut` | | |
| `[T]` | `split_once` | ⛔️ | nightly-only |
| `[T]` | `rsplit_once` | ⛔️ | nightly-only |
| `[T]` | `contains` | | |
| `[T]` | `starts_with` | | |
| `[T]` | `ends_with` | | |
| `[T]` | `strip_prefix` | | |
| `[T]` | `strip_suffix` | | |
| `[T]` | `strip_circumfix` | | |
| `[T]` | `trim_prefix` | | |
| `[T]` | `trim_suffix` | | |
| `[T]` | `binary_search` | | |
| `[T]` | `binary_search_by` | | |
| `[T]` | `binary_search_by_key` | | |
| `[T]` | `sort_unstable` | | |
| `[T]` | `sort_unstable_by` | | |
| `[T]` | `sort_unstable_by_key` | | |
| `[T]` | `partial_sort_unstable` | ⛔️ | nightly-only |
| `[T]` | `partial_sort_unstable_by` | ⛔️ | nightly-only |
| `[T]` | `partial_sort_unstable_by_key` | ⛔️ | nightly-only |
| `[T]` | `select_nth_unstable` | | |
| `[T]` | `select_nth_unstable_by` | | |
| `[T]` | `select_nth_unstable_by_key` | | |
| `[T]` | `partition_dedup` | ⛔️ | nightly-only |
| `[T]` | `partition_dedup_by` | ⛔️ | nightly-only |
| `[T]` | `partition_dedup_by_key` | ⛔️ | nightly-only |
| `[T]` | `rotate_left` | | |
| `[T]` | `rotate_right` | | |
| `[T]` | `shift_left` | ⛔️ | nightly-only |
| `[T]` | `shift_right` | ⛔️ | nightly-only |
| `[T]` | `fill` | | |
| `[T]` | `fill_with` | | |
| `[T]` | `clone_from_slice` | | |
| `[T]` | `copy_from_slice` | | |
| `[T]` | `copy_within` | | |
| `[T]` | `swap_with_slice` | | |
| `[T]` | `align_to` | | |
| `[T]` | `align_to_mut` | | |
| `[T]` | `as_simd` | ⛔️ | nightly-only |
| `[T]` | `as_simd_mut` | ⛔️ | nightly-only |
| `[T]` | `is_sorted` | | |
| `[T]` | `is_sorted_by` | | |
| `[T]` | `is_sorted_by_key` | | |
| `[T]` | `partition_point` | | |
| `[T]` | `split_off` | | |
| `[T]` | `split_off_mut` | | |
| `[T]` | `split_off_first` | | |
| `[T]` | `split_off_first_mut` | | |
| `[T]` | `split_off_last` | | |
| `[T]` | `split_off_last_mut` | | |
| `[T]` | `get_disjoint_unchecked_mut` | | |
| `[T]` | `get_disjoint_mut` | | |
| `[T]` | `element_offset` | | |
| `[T]` | `subslice_range` | | |
| `[T]` | `as_slice` | ⛔️ | nightly-only |
| `[T]` | `as_mut_slice` | ⛔️ | nightly-only |
| `[MaybeUninit<T>]` | `align_to_uninit_mut` | ⛔️ | nightly-only |
| `[[T; N]]` | `as_flattened` | | |
| `[[T; N]]` | `as_flattened_mut` | | |
| `[f32]` | `sort_floats` | ⛔️ | nightly-only |
| `[f64]` | `sort_floats` | ⛔️ | nightly-only |
| `[u8]` | `utf8_chunks` | | |
| `[T]` | `sort` | | |
| `[T]` | `sort_by` | | |
| `[T]` | `sort_by_key` | | |
| `[T]` | `sort_by_cached_key` | | |
| `[T]` | `to_vec` | | |
| `[T]` | `to_vec_in` | ⛔️ | nightly-only |
| `[T]` | `into_vec` | | |
| `[T]` | `repeat` | | |
| `[T]` | `concat` | | |
| `[T]` | `join` | | |
| `[T]` | `connect` | ⛔️ | deprecated |
| `[u8]` | `to_ascii_uppercase` | | |
| `[u8]` | `to_ascii_lowercase` | | |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Box<[T], A>` | `Clone` | | |
| `[T]` | `CloneToUninit` | ⛔️ | nightly-only |
| `[T]` | `ConstParamTy_` | ⛔️ | nightly-only |
| `[T]` | `Eq` | | |
| `[T]` | `PartialEq<[U]>` | | |
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
| `VecDeque<T, A>` | `PartialEq<&[U]>` | | |
| `VecDeque<T, A>` | `PartialEq<&mut [U]>` | | |
| `ByteStr` | `PartialEq<&[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<&[u8]>` | ⛔️ | nightly-only |
| `ByteStr` | `PartialEq<[u8]>` | ⛔️ | nightly-only |
| `[u8]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `&[u8]` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<[u8]>` | ⛔️ | nightly-only |
| `[u8]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `&[u8]` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `[T]` | `StructuralPartialEq` | ⛔️ | nightly-only |
| `[T]` | `Ord` | | |
| `[T]` | `PartialOrd` | | |
| `[T]` | `Hash` | | |
| `&[T]` | `Default` | | |
| `&mut [T]` | `Default` | | |
| `Box<[T]>` | `Default` | | |
| `[T]` | `Debug` | | |
| `[T]` | `AsRef<[T]>` | | |
| `[T; N]` | `AsRef<[T]>` | | |
| `Vec<T, A>` | `AsRef<[T]>` | | |
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
| `[T]` | `AsMut<[T]>` | | |
| `[T; N]` | `AsMut<[T]>` | | |
| `Vec<T, A>` | `AsMut<[T]>` | | |
| `MaybeUninit<[T; N]>` | `AsMut<[MaybeUninit<T>]>` | | |
| `Simd<T, N>` | `AsMut<[T]>` | ⛔️ | nightly-only |
| `ByteStr` | `AsMut<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `AsMut<[u8]>` | ⛔️ | nightly-only |
| `[T; N]` | `Borrow<[T]>` | | |
| `Vec<T, A>` | `Borrow<[T]>` | | |
| `ByteStr` | `Borrow<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `Borrow<[u8]>` | ⛔️ | nightly-only |
| `[T; N]` | `BorrowMut<[T]>` | | |
| `Vec<T, A>` | `BorrowMut<[T]>` | | |
| `ByteStr` | `BorrowMut<[u8]>` | ⛔️ | nightly-only |
| `ByteString` | `BorrowMut<[u8]>` | ⛔️ | nightly-only |
| `Box<[T]>` | `From<[T; N]>` | | |
| `Box<[T]>` | `From<&[T]>` | | |
| `Box<[T]>` | `From<&mut [T]>` | | |
| `Box<[T]>` | `From<Cow<'_, [T]>>` | | |
| `Box<[T], A>` | `From<Vec<T, A>>` | | |
| `Rc<[T]>` | `From<&[T]>` | | |
| `Rc<[T]>` | `From<&mut [T]>` | | |
| `Arc<[T]>` | `From<&[T]>` | | |
| `Arc<[T]>` | `From<&mut [T]>` | | |
| `Cow<'a, [T]>` | `From<&[T]>` | | |
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
| `&[T]` | `IntoIterator` | | |
| `&mut [T]` | `IntoIterator` | | |
| `Box<[T], A>` | `IntoIterator` | | |
| `&Box<[T], A>` | `IntoIterator` | | |
| `&mut Box<[T], A>` | `IntoIterator` | | |
| `Box<[T]>` | `FromIterator<T>` | | |
| `ByteString` | `FromIterator<&[u8]>` | ⛔️ | nightly-only |
| `[T]` | `Index<I>` | | |
| `[T]` | `IndexMut<I>` | | |
| `[T]` | `ToOwned` | | |
| `&[u8]` | `Read` | | |
| `&[u8]` | `BufRead` | | |
| `&mut [u8]` | `Write` | | |
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

## API parity with `Vec<T>`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Vec<T>` | `new` | | |
| `Vec<T>` | `with_capacity` | | |
| `Vec<T>` | `try_with_capacity` | ⛔️ | nightly-only |
| `Vec<T>` | `from_raw_parts` | | |
| `Vec<T>` | `from_parts` | | |
| `Vec<T>` | `from_fn` | | |
| `Vec<T>` | `into_raw_parts` | | |
| `Vec<T>` | `into_parts` | | |
| `Vec<T>` | `const_make_global` | ⛔️ | nightly-only |
| `Vec<T, A>` | `with_capacity_in` | | |
| `Vec<T, A>` | `push` | | |
| `Vec<T, A>` | `push_mut` | | |
| `Vec<T, A>` | `new_in` | | |
| `Vec<T, A>` | `try_with_capacity_in` | ⛔️ | nightly-only |
| `Vec<T, A>` | `from_raw_parts_in` | | |
| `Vec<T, A>` | `from_parts_in` | | |
| `Vec<T, A>` | `into_raw_parts_with_allocator` | | |
| `Vec<T, A>` | `into_parts_with_allocator` | | |
| `Vec<T, A>` | `capacity` | | |
| `Vec<T, A>` | `reserve` | | |
| `Vec<T, A>` | `reserve_exact` | | |
| `Vec<T, A>` | `try_reserve` | | |
| `Vec<T, A>` | `try_reserve_exact` | | |
| `Vec<T, A>` | `shrink_to_fit` | | |
| `Vec<T, A>` | `shrink_to` | | |
| `Vec<T, A>` | `try_shrink_to_fit` | ⛔️ | nightly-only |
| `Vec<T, A>` | `try_shrink_to` | ⛔️ | nightly-only |
| `Vec<T, A>` | `into_boxed_slice` | | |
| `Vec<T, A>` | `into_array` | ⛔️ | nightly-only |
| `Vec<T, A>` | `truncate` | | |
| `Vec<T, A>` | `as_slice` | | |
| `Vec<T, A>` | `as_mut_slice` | | |
| `Vec<T, A>` | `as_ptr` | | |
| `Vec<T, A>` | `as_mut_ptr` | | |
| `Vec<T, A>` | `as_non_null` | ⛔️ | nightly-only |
| `Vec<T, A>` | `allocator` | | |
| `Vec<T, A>` | `set_len` | | |
| `Vec<T, A>` | `swap_remove` | | |
| `Vec<T, A>` | `insert` | | |
| `Vec<T, A>` | `insert_mut` | | |
| `Vec<T, A>` | `remove` | | |
| `Vec<T, A>` | `try_remove` | ⛔️ | nightly-only |
| `Vec<T, A>` | `retain` | | |
| `Vec<T, A>` | `retain_mut` | | |
| `Vec<T, A>` | `dedup_by_key` | | |
| `Vec<T, A>` | `dedup_by` | | |
| `Vec<T, A>` | `push_within_capacity` | ⛔️ | nightly-only |
| `Vec<T, A>` | `pop` | | |
| `Vec<T, A>` | `pop_if` | | |
| `Vec<T, A>` | `peek_mut` | ⛔️ | nightly-only |
| `Vec<T, A>` | `append` | | |
| `Vec<T, A>` | `drain` | | |
| `Vec<T, A>` | `clear` | | |
| `Vec<T, A>` | `len` | | |
| `Vec<T, A>` | `is_empty` | | |
| `Vec<T, A>` | `split_off` | | |
| `Vec<T, A>` | `resize_with` | | |
| `Vec<T, A>` | `leak` | | |
| `Vec<T, A>` | `spare_capacity_mut` | | |
| `Vec<T, A>` | `split_at_spare_mut` | ⛔️ | nightly-only |
| `Vec<T, A>` | `into_chunks` | ⛔️ | nightly-only |
| `Vec<T, A>` | `recycle` | ⛔️ | nightly-only |
| `Vec<T, A>` | `resize` | | |
| `Vec<T, A>` | `extend_from_slice` | | |
| `Vec<T, A>` | `extend_from_within` | | |
| `Vec<[T; N], A>` | `into_flattened` | | |
| `Vec<T, A>` | `dedup` | | |
| `Vec<T, A>` | `splice` | | |
| `Vec<T, A>` | `extract_if` | | |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `Vec<T, A>` | `Clone` | | |
| `Vec<T, A>` | `Eq` | | |
| `Vec<T, A1>` | `PartialEq<Vec<U, A2>>` | | |
| `Vec<T, A>` | `PartialEq<[U]>` | | |
| `[T]` | `PartialEq<Vec<U, A>>` | | |
| `Vec<T, A>` | `PartialEq<[U; N]>` | | |
| `Vec<T, A>` | `PartialEq<&[U; N]>` | | |
| `Vec<T, A>` | `PartialEq<&[U]>` | | |
| `&[T]` | `PartialEq<Vec<U, A>>` | | |
| `Vec<T, A>` | `PartialEq<&mut [U]>` | | |
| `&mut [T]` | `PartialEq<Vec<U, A>>` | | |
| `Cow<'_, [T]>`| `PartialEq<Vec<U, A>>` | | |
| `Vec<T, A>` | `PartialEq<Cow<'_, [U]>>` | | |
| `VecDeque<T, A>` | `PartialEq<Vec<U, A>>` | | |
| `Vec<u8>` | `PartialEq<ByteStr>` | ⛔️ | nightly-only |
| `ByteStr` | `PartialEq<Vec<u8>>` | ⛔️ | nightly-only |
| `Vec<u8>` | `PartialEq<ByteString>` | ⛔️ | nightly-only |
| `ByteString` | `PartialEq<Vec<u8>>` | ⛔️ | nightly-only |
| `Vec<T, A>` | `Ord` | | |
| `Vec<T, A1>` | `PartialOrd<Vec<T, A2>>` | | |
| `Vec<T, A>` | `Hash` | | |
| `Vec<T>` | `Default` | | |
| `Vec<T, A>` | `Drop` | | |
| `Vec<T, A>` | `Debug` | | |
| `Vec<T, A>` | `Deref` | | |
| `Vec<T, A>` | `DerefMut` | | |
| `Vec<T, A>` | `DerefPure` | ⛔️ | nightly-only |
| `Vec<T, A>` | `AsRef<Vec<T, A>>` | | |
| `Vec<T, A>` | `AsRef<[T]>` | | |
| `Vec<T, A>` | `AsMut<Vec<T, A>>` | | |
| `Vec<T, A>` | `AsMut<[T]>` | | |
| `Vec<T, A>` | `Borrow<[T]>` | | |
| `Vec<T, A>` | `BorrowMut<[T]>` | | |
| `Cow<'_, [T]>` | `From<&Vec<T>>` | | |
| `Vec<T>` | `From<[T; N]>` | | |
| `Vec<T>` | `From<&[T]>` | | |
| `Vec<T>` | `From<&[T; N]>` | | |
| `Vec<T>` | `From<&mut [T]>` | | |
| `Vec<T>` | `From<&mut [T; N]>` | | |
| `Vec<T, A>` | `From<Box<[T], A>>` | | |
| `Vec<T>` | `From<Cow<'a, [T]>>` | | |
| `Rc<[T], A>` | `From<Vec<T, A>>` | | |
| `Arc<[T], A>` | `From<Vec<T, A>>` | | |
| `Box<[T], A>` | `From<Vec<T, A>>` | | |
| `Cow<'_, [T]>` | `From<Vec<T>>` | | |
| `Vec<T, A>` | `From<VecDeque<T, A>>` | | |
| `VecDeque<T, A>` | `From<Vec<T, A>>` | | |
| `Vec<T, A>` | `From<BinaryHeap<T, A>>` | | |
| `BinaryHeap<T, A>` | `From<Vec<T, A>>` | | |
| `CString` | `From<Vec<NonZero<u8>>>` | | |
| `Vec<u8>` | `From<&str>` | | |
| `Vec<u8>` | `From<String>` | | |
| `Vec<u8>` | `From<CString>` | | |
| `Vec<u8>` | `From<ByteString>` | ⛔️ | nightly-only |
| `[T; N]` | `TryFrom<Vec<T, A>>` | | |
| `Box<[T; N], A>` | `TryFrom<Vec<T, A>>` | | |
| `String` | `TryFrom<Vec<u8>>` | | |
| Vec<T, A>| `IntoIterator` | | |
| &Vec<T, A> | `IntoIterator` | | |
| &mut Vec<T, A> | `IntoIterator` | | |
| `Vec<T>` | `FromIterator<T>` | | |
| `Vec<T, A>` | `Index<I>` | | |
| `Vec<T, A>` | `IndexMut<I>` | | |
| `Vec<T, A>` | `Extend<T>` | | |
| `Vec<T, A>` | `Extend<&T>` | | |
| `Vec<u8, A>` | `Write` | | |
