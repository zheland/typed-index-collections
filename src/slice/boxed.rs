#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec};
use core::iter::FromIterator;
use core::mem::transmute;

#[cfg(any(feature = "serde-alloc", feature = "serde-std"))]
use serde::de::{Deserialize, Deserializer};

use crate::{TiSlice, TiVec};

impl<K, V> From<Box<TiSlice<K, V>>> for Box<[V]> {
    #[inline]
    fn from(slice: Box<TiSlice<K, V>>) -> Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { transmute::<Box<TiSlice<K, V>>, Self>(slice) }
    }
}

impl<K, V> From<Box<[V]>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(slice: Box<[V]>) -> Self {
        // SAFETY: `TiSlice<K, V>` is `repr(transparent)` over a `[V]` type.
        unsafe { transmute::<Box<[V]>, Self>(slice) }
    }
}

impl<K, V: Clone> Clone for Box<TiSlice<K, V>> {
    #[inline]
    fn clone(&self) -> Self {
        self.to_vec().into_boxed_slice()
    }
}

impl<K, V> IntoIterator for Box<TiSlice<K, V>> {
    type Item = V;
    type IntoIter = vec::IntoIter<V>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<K, V> Default for Box<TiSlice<K, V>> {
    #[inline]
    fn default() -> Self {
        TiVec::new().into()
    }
}

impl<K, V: Copy> From<&TiSlice<K, V>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(slice: &TiSlice<K, V>) -> Self {
        Box::<[V]>::from(&slice.raw).into()
    }
}

impl<K, V> From<Box<TiSlice<K, V>>> for TiVec<K, V> {
    #[inline]
    fn from(s: Box<TiSlice<K, V>>) -> Self {
        s.into_vec()
    }
}

impl<K, V> From<TiVec<K, V>> for Box<TiSlice<K, V>> {
    #[inline]
    fn from(v: TiVec<K, V>) -> Self {
        v.into_boxed_slice()
    }
}

impl<K, V> FromIterator<V> for Box<TiSlice<K, V>> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = V>>(iter: T) -> Self {
        iter.into_iter().collect::<TiVec<K, V>>().into_boxed_slice()
    }
}

#[cfg(feature = "serde-alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde-alloc")))]
impl<'de, K, V: Deserialize<'de>> Deserialize<'de> for Box<TiSlice<K, V>> {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Box::<[V]>::deserialize(deserializer).map(Into::into)
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
    use crate::{TiSlice, TiVec};

    #[test]
    fn test_boxed_slice_api_compatibility() {
        for v in [
            &[0_u32; 0][..],
            &[1],
            &[1, 1234],
            &[1, 2, 4],
            &[1, 5, 3, 2],
            &[1, 1, 9, 2, 4, 1, 12345, 12],
        ] {
            let mut cv = (v, TiSlice::from_ref(v));
            assert_eq_api!(
                cv, v => Box::<TheSlice<u32>>::from(v) == <Box<TheSlice<u32>>>::default()
            );
            assert_eq_api!(cv, v => Box::<TheSlice<_>>::from(v).into_std());
            assert_eq_api!(cv, v => Box::<TheSlice<_>>::from(v).clone().into_std());
            assert_eq_api!(
                cv, v => IntoIterator::into_iter(Box::<TheSlice<u32>>::from(v)).collect::<Vec<_>>()
            );
            assert_eq_api!(cv, v => TheVec::from(Box::<TheSlice<_>>::from(v)).into_std());
            assert_eq_api!(cv, v => Box::<TheSlice<_>>::from(TheVec::from(v)).into_std());
            assert_eq_api!(cv, v => v.iter().copied().collect::<Box<TheSlice<_>>>().into_std());
        }
    }

    #[expect(clippy::unwrap_used, reason = "okay in tests")]
    #[cfg(feature = "serde")]
    #[test]
    fn test_boxed_slice_deserialize() {
        let s0: Box<TiSlice<Id, u32>> = serde_json::from_str("[]").unwrap();
        let s1: Box<TiSlice<Id, u32>> = serde_json::from_str("[12]").unwrap();
        let s2: Box<TiSlice<Id, u32>> = serde_json::from_str("[23, 34]").unwrap();
        assert_eq!(s0.as_ref().raw, [0; 0][..]);
        assert_eq!(s1.as_ref().raw, [12][..]);
        assert_eq!(s2.as_ref().raw, [23, 34][..]);
    }
}
