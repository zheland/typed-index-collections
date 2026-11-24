# Development

## API parity with `[T; N]`

| Type | Method | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `[T; N]` | `map` | ✅ | |
| `[T; N]` | `as_slice` | ✅ | |
| `[T; N]` | `as_mut_slice` | ✅ | |
| `[T; N]` | `each_ref` | ✅ | |
| `[T; N]` | `each_mut` | ✅ | |
| `[T; N]` | `try_map` | ⛔️ | Nightly-only |
| `[T; N]` | `transpose` | ⛔️ | Nightly-only |
| `[T; N]` | `rsplit_array_mut` | ⛔️ | Nightly-only |
| `[T; N]` | `rsplit_array_ref` | ⛔️ | Nightly-only |
| `[T; N]` | `split_array_mut` | ⛔️ | Nightly-only |
| `[T; N]` | `split_array_ref` | ⛔️ | Nightly-only |
| `[u8; N]` | `as_ascii` | ⛔️ | Nightly-only |
| `[u8; N]` | `as_ascii_unchecked` | ⛔️ | Nightly-only |
| `[MaybeUninit<T>; N]` | `transpose` | ⛔️ | Nightly-only |

| Type | Trait | Implemented | Notes |
|:--:|:--:|:--:|:--:|
| `[T; N]` | `Copy` | ✅ | |
| `[T; N]` | `Clone` | ✅ | |
| `[T; N]` | `CloneFromCell` | ⛔️ | Nightly-only |
| `[T; N]` | `ConstParamTy_` | ⛔️ | Nightly-only |
| `[T; N]` | `Clone` | ✅ | |
| `[T; N]` | `Eq` | ✅ | |
| `[T; N]` | `PartialEq<[U; N]>` | ✅ | |
| `[T; N]` | `PartialEq<[U]>` | ✅ | |
| `[T; N]` | `PartialEq<&[U]>` | ✅ | |
| `[T; N]` | `PartialEq<&mut [U]>` | ✅ | |
| `[u8; N]` | `PartialEq<ByteStr>` | ⛔️ | Nightly-only |
| `&[u8; N]` | `PartialEq<ByteStr>` | ⛔️ | Nightly-only |
| `[u8; N]` | `PartialEq<ByteString>` | ⛔️ | Nightly-only |
| `&[u8; N]` | `PartialEq<ByteString>` | ⛔️ | Nightly-only |
| `[u8; N]` | `StructuralPartialEq` | ⛔️ | Nightly-only |
| `[T; N]` | `Ord` | ✅ | |
| `[T; N]` | `PartialOrd` | ✅ | |
| `[T; N]` | `Hash` | ✅ | |
| `[T; N]` | `Debug` | ✅ | |
| `[T; N]` | `AsRef<Self>` | ✅ | |
| `[T; N]` | `AsMut<Self>` | ✅ | |
| `[T; N]` | `AsRef<[T]>` | ✅ | |
| `[T; N]` | `AsMut<[T]>` | ✅ | |
| `Cell<[T; N]>` | `AsRef<[Cell<T>; N]>` | ✅ | |
| `Cell<[T; N]>` | `AsMut<[Cell<T>; N]>` | ✅ | |
| `MaybeUninit<[T; N]>` | `AsRef<[MaybeUninit<T>; N]>` | ✅ | |
| `MaybeUninit<[T; N]>` | `AsMut<[MaybeUninit<T>; N]>` | ✅ | |
| `Simd<T, N>` | `AsRef<[T; N]>` | ⛔️ | Nightly-only |
| `Simd<T, N>` | `AsMut<[T; N]>` | ⛔️ | Nightly-only |
| `[T; N]` | `Borrow<[T]>` | ✅ | |
| `[T; N]` | `BorrowMut<[T]>` | ✅ | |
| `MaybeUninit<[MaybeUninit<T>; N]>` | `From<[T; N]>` | ✅ | |
| `MaybeUninit<[T; N]>` | `From<[MaybeUninit<T>; N]>` | ✅ | |
| `[T; N]` | `From<(T₁, T₂, …, Tₙ)>` | ✅ | |
| `[bool; N]` | `From<Mask<T, N>>` | ⛔️ | Nightly-only |
| `[T; N]` | `TryFrom<&[T]>` | ✅ | |
| `[T; N]` | `TryFrom<&mut [T]>` | ✅ | |
| `&[T; N]` | `TryFrom<&[T]>` | ✅ | |
| `&mut [T; N]` | `TryFrom<&mut [T]>` | ✅ | |
| `[T; N]` | `TryFrom<Vec<T>>` | ✅ | |
| `Box<[T; N]>` | `TryFrom<Vec<T>>` | ✅ | |
| `[T; N]` | `Index<I>` | ✅ | |
| `[T; N]` | `IndexMut<I>` | ✅ | |
| `[T; N]` | `IntoIterator` | ✅ | |
| `&[T; N]` | `IntoIterator` | ✅ | |
| `&mut [T; N]` | `IntoIterator` | ✅ | |
| `Box<[T; N]>` | `IntoIterator` | ✅ | |
| `&Box<[T; N]>` | `IntoIterator` | ✅ | |
| `&mut Box<[T; N]>` | `IntoIterator` | ✅ | |
| `[char; N]` | `Pattern` | ⛔️ | Nightly-only |
| `&[char; N]` | `Pattern` | ⛔️ | Nightly-only |

## API parity with `[T]`

## API parity with `Vec<T>`
