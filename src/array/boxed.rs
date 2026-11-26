use core::alloc::Allocator;
use core::mem::{transmute_copy, ManuallyDrop};
use core::slice;

use alloc::boxed::{self, Box};

use crate::TiArray;

impl<K, V, A: Allocator, const N: usize> IntoIterator for Box<TiArray<K, V, N>, A> {
    type Item = V;
    type IntoIter = boxed::BoxedArrayIntoIter<V, N, A>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        // `transmute_copy` used instead of `transmute` because Rust can not
        // prove the size equality because of `A`.
        let array = ManuallyDrop::new(self);
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]`
        // type.
        let array = unsafe { transmute_copy::<ManuallyDrop<Self>, Box<[V; N], A>>(&array) };
        array.into_iter()
    }
}

impl<'a, K, V, A: Allocator, const N: usize> IntoIterator for &'a Box<TiArray<K, V, N>, A> {
    type Item = &'a V;
    type IntoIter = slice::Iter<'a, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.raw.as_slice().iter()
    }
}

impl<'a, K, V, A: Allocator, const N: usize> IntoIterator for &'a mut Box<TiArray<K, V, N>, A> {
    type Item = &'a mut V;
    type IntoIter = slice::IterMut<'a, V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.raw.as_mut_slice().iter_mut()
    }
}

#[expect(dead_code, unused_imports, unused_mut, reason = "okay in tests")]
#[cfg(test)]
mod test {
    use alloc::borrow::{Cow, ToOwned};
    use alloc::boxed::Box;
    use alloc::ffi::CString;
    use alloc::string::ToString;
    use alloc::vec::Vec;
    use core::borrow::{Borrow, BorrowMut};
    use core::hash::{Hash, Hasher};
    use core::ops::Bound;
    #[cfg(feature = "std")]
    use std::hash::DefaultHasher;
    #[cfg(feature = "std")]
    use std::io::{IoSlice, Write};

    use crate::test_util::{AsSliceAndCapacity, Id};
    use crate::{TiArray, TiSlice, TiVec};

    #[test]
    fn test_array_read_core_api_compatibility() {
        test_boxed_array_api_compatibility_impl([]);
        test_boxed_array_api_compatibility_impl([1]);
        test_boxed_array_api_compatibility_impl([1, 1234]);
        test_boxed_array_api_compatibility_impl([1, 2, 4]);
        test_boxed_array_api_compatibility_impl([1, 5, 3, 2]);
        test_boxed_array_api_compatibility_impl([1, 1, 9, 2, 4, 1, 12345, 12]);
    }

    #[inline]
    fn test_boxed_array_api_compatibility_impl<const N: usize>(v: [u32; N]) {
        let cv = (v, TiArray::from_array(v));
        let mut cv = (&cv.0, &cv.1);

        assert_eq_api!(
            cv, v => IntoIterator::into_iter(Box::<TheArray<u32, N>>::new(*v)).collect::<Vec<_>>()
        );
    }

    #[expect(clippy::unwrap_used, reason = "okay in tests")]
    #[cfg(feature = "serde")]
    #[test]
    fn test_boxed_slice_deserialize() {
        use crate::TiArray;

        let s0: Box<TiArray<Id, u32, 0>> = serde_json::from_str("[]").unwrap();
        let s1: Box<TiArray<Id, u32, 1>> = serde_json::from_str("[12]").unwrap();
        let s2: Box<TiArray<Id, u32, 2>> = serde_json::from_str("[23, 34]").unwrap();
        assert_eq!(s0.as_ref().raw, [0; 0][..]);
        assert_eq!(s1.as_ref().raw, [12][..]);
        assert_eq!(s2.as_ref().raw, [23, 34][..]);
    }

    #[expect(clippy::unwrap_used, reason = "okay in tests")]
    #[cfg(feature = "bincode")]
    #[test]
    fn test_boxed_slice_decode() {
        use crate::TiArray;

        fn decode_whole<const N: usize>(bytes: &[u8]) -> Box<TiArray<Id, u32, N>> {
            let config = bincode::config::standard();
            let (decoded, len) = bincode::decode_from_slice(bytes, config).unwrap();
            assert_eq!(len, bytes.len());
            decoded
        }

        let s0: Box<TiArray<Id, u32, 0>> = decode_whole(&[]);
        let s1: Box<TiArray<Id, u32, 1>> = decode_whole(&[12]);
        let s2: Box<TiArray<Id, u32, 2>> = decode_whole(&[23, 34]);
        let s3: Box<TiArray<Id, u32, 2>> =
            decode_whole(&[252, 0x78, 0x56, 0x34, 0x12, 252, 0x89, 0x67, 0x45, 0x23]);
        assert_eq!(s0.as_ref().raw, [0; 0][..]);
        assert_eq!(s1.as_ref().raw, [12][..]);
        assert_eq!(s2.as_ref().raw, [23, 34][..]);
        assert_eq!(s3.as_ref().raw, [0x1234_5678, 0x2345_6789][..]);
    }
}
