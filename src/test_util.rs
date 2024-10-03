// This module is used only for tests.

use alloc::vec::Vec;

use derive_more::{From, Into};

use crate::TiSlice;

#[derive(From, Into, Clone, Copy, Debug, Eq, PartialEq)]
pub struct Id(usize);

pub trait IntoStdType {
    type Std;
    fn into_std(self) -> Self::Std;
}

pub trait IntoTicType {
    type Tic;
    fn into_tic(self) -> Self::Tic;
}

pub trait MapIntoStdType {
    type StdIter;
    fn map_into_std(self) -> Self::StdIter;
}

impl<I, T> MapIntoStdType for I
where
    I: IntoIterator<Item = T>,
    T: IntoStdType,
{
    type StdIter = MapIntoStdIter<I::IntoIter>;

    fn map_into_std(self) -> Self::StdIter {
        MapIntoStdIter(self.into_iter())
    }
}

pub struct MapIntoStdIter<I>(I);

impl<I, T> Iterator for MapIntoStdIter<I>
where
    I: Iterator<Item = T>,
    T: IntoStdType,
{
    type Item = T::Std;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(T::into_std)
    }
}

pub trait FakeConversion: Sized {
    fn into_std(self) -> Self {
        self
    }

    fn into_tic(self) -> Self {
        self
    }

    fn map_into_std(self) -> Self {
        self
    }
}

impl<T> FakeConversion for T {}

pub trait CollectToVec: Sized + IntoIterator {
    fn collect_to_vec(self) -> Vec<<Self as IntoIterator>::Item> {
        self.into_iter().collect()
    }
}

impl<T> CollectToVec for T where T: IntoIterator {}

pub trait Reborrow {
    type Output<'a>
    where
        Self: 'a;
    fn reborrow(&mut self) -> Self::Output<'_>;
}

impl<T> Reborrow for &T
where
    T: ?Sized,
{
    type Output<'a>
        = &'a T
    where
        Self: 'a;

    fn reborrow(&mut self) -> Self::Output<'_> {
        &**self
    }
}

impl<T> Reborrow for &mut T
where
    T: ?Sized,
{
    type Output<'a>
        = &'a mut T
    where
        Self: 'a;

    fn reborrow(&mut self) -> Self::Output<'_> {
        &mut **self
    }
}

pub trait AsSliceAndCapacity {
    type Item;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize);
}

impl<T> AsSliceAndCapacity for &T
where
    T: ?Sized + AsSliceAndCapacity,
{
    type Item = T::Item;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        T::as_slice_and_capacity(self)
    }
}

impl<T> AsSliceAndCapacity for &mut T
where
    T: ?Sized + AsSliceAndCapacity,
{
    type Item = T::Item;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        T::as_slice_and_capacity(self)
    }
}

impl<T> AsSliceAndCapacity for [T] {
    type Item = T;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        (self, self.len())
    }
}

impl<K, V> AsSliceAndCapacity for TiSlice<K, V> {
    type Item = V;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        (self.as_ref(), self.len())
    }
}

#[cfg(feature = "alloc")]
impl<T> AsSliceAndCapacity for Vec<T> {
    type Item = T;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        let capacity = self.capacity();
        (self, capacity)
    }
}

#[cfg(feature = "alloc")]
impl<K, V> AsSliceAndCapacity for crate::TiVec<K, V> {
    type Item = V;
    fn as_slice_and_capacity(&self) -> (&[Self::Item], usize) {
        let capacity = self.capacity();
        (self.as_ref(), capacity)
    }
}

macro_rules! impl_into_std {
    (
        $( for [$($args:tt)*] )?,
        $source:ty => $target:ty,
        $self:ident => $expr:expr
        $(, where $($bounds:tt)* )?
    ) => {
        impl $( < $($args)* > )? IntoStdType for $source
        $( where $($bounds)* )?
        {
            type Std = $target;
            fn into_std($self) -> Self::Std {
                $expr
            }
        }
    };
}

macro_rules! impl_into_tic {
    (
        $( for [ $($args:tt)* ] )?,
        $source:ty => $target:ty,
        $self:ident => $expr:expr
        $(, where $($bounds:tt)* )?
    ) => {
        impl $( < $($args)* > )? IntoTicType for $source
        $( where $($bounds)* )?
        {
            type Tic = $target;
            fn into_tic($self) -> Self::Tic {
                $expr
            }
        }
    };
}

mod core_impls {
    #[cfg(feature = "alloc")]
    use alloc::borrow::Cow;
    use core::ops::{Bound, Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive};

    use crate::test_util::{Id, IntoStdType, IntoTicType};
    use crate::TiSlice;

    impl_into_tic!(, usize => Id, self => self.into());
    impl_into_std!(, Id => usize, self => self.into());
    impl_into_tic!(for ['a, T], &'a [T] => &'a TiSlice<Id, T>, self => self.as_ref());
    impl_into_std!(for ['a, T], &'a TiSlice<Id, T> => &'a [T], self => self.as_ref());
    impl_into_tic!(for ['a, T], &'a mut [T] => &'a mut TiSlice<Id, T>, self => self.as_mut());
    impl_into_std!(for ['a, T], &'a mut TiSlice<Id, T> => &'a mut [T], self => self.as_mut());

    impl_into_tic!(,
        Range<usize> => Range<Id>,
        self => self.start.into_tic()..self.end.into_tic()
    );
    impl_into_tic!(,
        RangeInclusive<usize> => RangeInclusive<Id>,
        self => self.start().into_tic()..=self.end().into_tic()
    );
    impl_into_tic!(,RangeFrom<usize> => RangeFrom<Id>, self => self.start.into_tic()..);
    impl_into_tic!(,RangeTo<usize> => RangeTo<Id>, self => ..self.end.into_tic());
    impl_into_tic!(,
        RangeToInclusive<usize> => RangeToInclusive<Id>,
        self => ..=self.end.into_tic()
    );
    impl_into_tic!(,
        (Bound<usize>, Bound<usize>) => (Bound<Id>, Bound<Id>),
        self => (self.0.into_tic(), self.1.into_tic())
    );
    impl_into_tic!(,
        Bound<usize> => Bound<Id>,
        self => match self {
            Bound::Included(index) => Bound::Included(index.into_tic()),
            Bound::Excluded(index) => Bound::Excluded(index.into_tic()),
            Bound::Unbounded => Bound::Unbounded,
        }
    );

    impl_into_tic!(
        for [T, U],
        Option<T> => Option<U>,
        self => self.map(IntoTicType::into_tic),
        where T: IntoTicType<Tic = U>
    );
    impl_into_std!(
        for [T, U],
        Option<T> => Option<U>,
        self => self.map(IntoStdType::into_std),
        where T: IntoStdType<Std = U>
    );
    impl_into_tic!(
        for [T, U, E, Y],
        Result<T, E> => Result<U, Y>,
        self => self.map(IntoTicType::into_tic).map_err(IntoTicType::into_tic),
        where T: IntoTicType<Tic = U>, E: IntoTicType<Tic = Y>
    );
    impl_into_std!(
        for [T, U, E, Y],
        Result<T, E> => Result<U, Y>,
        self => self.map(IntoStdType::into_std).map_err(IntoStdType::into_std),
        where T: IntoStdType<Std = U>, E: IntoStdType<Std = Y>
    );

    #[cfg(feature = "alloc")]
    impl_into_std!(
        for ['a, T], Cow<'a, TiSlice<Id, T>> => Cow<'a, [T]>,
        self => match self {
            Cow::Borrowed(value) => Cow::Borrowed(value.as_ref()),
            Cow::Owned(value) => Cow::Owned(value.into()),
        },
        where T: Clone
    );

    impl_into_std!(
        for ['a, T, U],
        (&'a TiSlice<Id, T>, &'a TiSlice<Id, U>) => (&'a [T], &'a [U]),
        self => (self.0.into_std(), self.1.into_std())
    );
    impl_into_std!(
        for ['a, T, U],
        (&'a mut TiSlice<Id, T>, &'a mut TiSlice<Id, U>) => (&'a mut [T], &'a mut [U]),
        self => (self.0.into_std(), self.1.into_std())
    );
    impl_into_std!(
        for ['a, T, U, V],
        (&'a TiSlice<Id, T>, &'a TiSlice<Id, U>, &'a TiSlice<Id, V>) => (&'a [T], &'a [U], &'a [V]),
        self => (self.0.into_std(), self.1.into_std(), self.2.into_std())
    );
    impl_into_std!(
        for ['a, T, U, V],
        (
            &'a mut TiSlice<Id, T>, &'a mut TiSlice<Id, U>, &'a mut TiSlice<Id, V>
        ) => (&'a mut [T], &'a mut [U], &'a mut [V]),
        self => (self.0.into_std(), self.1.into_std(), self.2.into_std())
    );

    impl_into_std!(
        for ['a, T],
        (&'a T, &'a TiSlice<Id, T>) => (&'a T, &'a [T]),
        self => (self.0, self.1.into_std())
    );
    impl_into_std!(
        for ['a, T],
        (&'a mut T, &'a mut TiSlice<Id, T>) => (&'a mut T, &'a mut [T]),
        self => (self.0, self.1.into_std())
    );
    impl_into_std!(
        for ['a, T, U, V],
        (&'a TiSlice<Id, T>, &'a U, &'a TiSlice<Id, V>) => (&'a [T], &'a U, &'a [V]),
        self => (self.0.into_std(), self.1, self.2.into_std())
    );
    impl_into_std!(
        for ['a, T, U, V],
        (
            &'a mut TiSlice<Id, T>, &'a mut U, &'a mut TiSlice<Id, V>
        ) => (&'a mut [T], &'a mut U, &'a mut [V]),
        self => (self.0.into_std(), self.1, self.2.into_std())
    );

    #[cfg(feature = "alloc")]
    impl_into_std!(
        for ['a, T],
        alloc::vec::Vec<&'a TiSlice<Id, T>> => alloc::vec::Vec<&'a [T]>,
        self => self.into_iter().map(TiSlice::as_ref).collect()
    );
    #[cfg(feature = "alloc")]
    impl_into_std!(
        for ['a, T],
        alloc::vec::Vec<&'a mut TiSlice<Id, T>> => alloc::vec::Vec<&'a mut [T]>,
        self => self.into_iter().map(TiSlice::as_mut).collect()
    );
}

#[cfg(feature = "alloc")]
mod alloc_impls {
    use alloc::boxed::Box;
    use alloc::vec::Vec;

    use crate::test_util::{Id, IntoStdType, IntoTicType};
    use crate::{TiSlice, TiVec};

    impl_into_tic!(for [T], Box<[T]> => Box<TiSlice<Id, T>>, self => self.into());
    impl_into_std!(for [T], Box<TiSlice<Id, T>> => Box<[T]>, self => self.into());
    impl_into_tic!(for [T], Vec<T> => TiVec<Id, T>, self => self.into());
    impl_into_std!(for [T], TiVec<Id, T> => Vec<T>, self => self.into());
    impl_into_tic!(for ['a, T], &'a Vec<T> => &'a TiVec<Id, T>, self => self.as_ref());
    impl_into_std!(for ['a, T], &'a TiVec<Id, T> => &'a Vec<T>, self => self.as_ref());
    impl_into_tic!(for ['a, T], &'a mut Vec<T> => &'a mut TiVec<Id, T>, self => self.as_mut());
    impl_into_std!(for ['a, T], &'a mut TiVec<Id, T> => &'a mut Vec<T>, self => self.as_mut());
}

macro_rules! assert_eq_api {
    ($in_value:expr, $in_arg:ident => $expr:expr) => {{
        let (std_in, tic_in) = (
            $crate::test_util::Reborrow::reborrow(&mut $in_value.0),
            $crate::test_util::Reborrow::reborrow(&mut $in_value.1),
        );
        let mut $in_arg = std_in;
        let std_out = {
            use crate::test_util::FakeConversion;
            type TheSlice<T> = [T];
            #[cfg(feature = "alloc")]
            type TheVec<T> = alloc::vec::Vec<T>;
            $expr
        };
        let mut $in_arg = tic_in;
        let tic_out = {
            use crate::test_util::{IntoStdType, IntoTicType, MapIntoStdType};
            type TheSlice<T> = crate::TiSlice<crate::test_util::Id, T>;
            #[cfg(feature = "alloc")]
            type TheVec<T> = crate::TiVec<crate::test_util::Id, T>;
            $expr
        };

        assert_eq!(tic_out, std_out, "where expr: {}", stringify!($expr));
        assert_eq!(
            crate::test_util::AsSliceAndCapacity::as_slice_and_capacity(&$in_value.0),
            crate::test_util::AsSliceAndCapacity::as_slice_and_capacity(&$in_value.1),
            "where expr: {}",
            stringify!($expr)
        );
    }};
}
