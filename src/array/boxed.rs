use core::alloc::Allocator;
use core::mem::{transmute, transmute_copy, ManuallyDrop};
use core::slice;

use alloc::boxed::{self, Box};
use alloc::vec::Vec;

use crate::{TiArray, TiVec};

impl<K, V, A: Allocator, const N: usize> TryFrom<TiVec<K, V, A>> for TiArray<K, V, N> {
    type Error = TiVec<K, V, A>;

    #[inline]
    fn try_from(vec: TiVec<K, V, A>) -> Result<Self, Self::Error> {
        Ok(Self::from(<[V; N]>::try_from(Vec::from(vec))?))
    }
}

impl<K, V, A: Allocator, const N: usize> TryFrom<TiVec<K, V, A>> for Box<TiArray<K, V, N>> {
    type Error = TiVec<K, V, A>;

    #[inline]
    fn try_from(vec: TiVec<K, V, A>) -> Result<Self, Self::Error> {
        let boxed: Box<[V; N]> = <[V; N]>::try_from(Vec::from(vec))?.into();
        // SAFETY: `TiArray<K, V, N>` is `repr(transparent)` over a `[V; N]`
        // type.
        Ok(unsafe { transmute::<Box<[V; N]>, Self>(boxed) })
    }
}

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
