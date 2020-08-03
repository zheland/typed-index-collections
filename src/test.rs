// This module is used only for tests.

#[cfg(any(feature = "alloc", feature = "std"))]
use alloc::{boxed::Box, vec::Vec};

#[cfg(feature = "impl-index-from")]
use derive_more::{From, Into};

use crate::TiSlice;

#[cfg(not(feature = "impl-index-from"))]
use crate::Index;

#[cfg(any(feature = "alloc", feature = "std"))]
use crate::TiVec;

#[cfg_attr(feature = "impl-index-from", derive(From, Into))]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Id(usize);

#[cfg(not(feature = "impl-index-from"))]
impl Index for Id {
    fn from_usize(index: usize) -> Self {
        Self(index)
    }

    fn into_usize(self) -> usize {
        self.0
    }
}

pub trait DummyConvert {
    type Target;
    fn into_t(self) -> Self::Target;
}

pub trait TypedConvert {
    type Target;
    fn into_t(self) -> Self::Target;
}

impl<'a, T> DummyConvert for T {
    type Target = T;
    fn into_t(self) -> Self::Target {
        self
    }
}

macro_rules! impl_convert_impl {
    (($($args:tt)*)($self:ident)($source:ty)($target:ty)($($where:tt)*)($($body:tt)*)) => {
        impl $($args)* TypedConvert for $source $($where)* {
            type Target = $target;
            fn into_t($self) -> Self::Target {
                $($body)*
            }
        }
    };
}

macro_rules! impl_convert {
    (|$self:ident: $source:ty| -> $target:ty { $($body:tt)* } ) => {
        impl_convert_impl!(()($self)($source)($target)()($($body)*));
    };
    (for ($($args:tt)*) |$self:ident: $source:ty| -> $target:ty { $($body:tt)* } ) => {
        impl_convert_impl!((<$($args)*>)($self)($source)($target)()($($body)*));
    };
    (for ($($args:tt)*) |$self:ident: $source:ty| -> $target:ty
        where ( $($bounds:tt)* ) { $($body:tt)* }
    ) => {
        impl_convert_impl!((<$($args)*>)($self)($source)($target)
            (where $($bounds)*)($($body)*));
    };
}

#[cfg(not(feature = "impl-index-from"))]
impl_convert!(|self: usize| -> Id { Id::from_usize(self) });
#[cfg(feature = "impl-index-from")]
impl_convert!(|self: usize| -> Id { self.into() });

#[cfg(not(feature = "impl-index-from"))]
impl_convert!(|self: Id| -> usize { self.into_usize() });
#[cfg(feature = "impl-index-from")]
impl_convert!(|self: Id| -> usize { self.into() });

impl_convert!(for ('a, V)
    |self: &'a [V]| -> &'a TiSlice<Id, V> { self.as_ref() });
impl_convert!(for ('a, V)
    |self: &'a TiSlice<Id, V>| -> &'a [V] { self.as_ref() });

impl_convert!(for ('a, V)
    |self: &'a mut [V]| -> &'a mut TiSlice<Id, V> { self.as_mut() });
impl_convert!(for ('a, V)
    |self: &'a mut TiSlice<Id, V>| -> &'a mut [V] { self.as_mut() });

#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for (V)
    |self: Box<[V]>| -> Box<TiSlice<Id, V>> { self.into() });
#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for (V)
    |self: Box<TiSlice<Id, V>>| -> Box<[V]> { self.into() });

#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for (T) |self: Vec<T>| -> TiVec<Id, T> { self.into() } );
#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for (T) |self: TiVec<Id, T>| -> Vec<T> { self.into() } );

#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for ('a, T) |self: &'a Vec<T>| -> &'a TiVec<Id, T> { self.as_ref() } );
#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for ('a, T) |self: &'a TiVec<Id, T>| -> &'a Vec<T> { self.as_ref() } );

#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for ('a, T) |self: &'a mut Vec<T>| -> &'a mut TiVec<Id, T> { self.as_mut() } );
#[cfg(any(feature = "alloc", feature = "std"))]
impl_convert!(for ('a, T) |self: &'a mut TiVec<Id, T>| -> &'a mut Vec<T> { self.as_mut() } );

impl_convert!(for ('a, V)
    |self: (&'a V, &'a TiSlice<Id, V>)| -> (&'a V, &'a [V]) {
        (self.0, self.1.as_ref())
    }
);
impl_convert!(for ('a, V)
    |self: (&'a mut V, &'a mut TiSlice<Id, V>)| -> (&'a mut V, &'a mut [V]) {
        (self.0, self.1.as_mut())
    }
);

impl_convert!(for ('a, V, U)
    |self: (&'a TiSlice<Id, V>, &'a TiSlice<Id, U>)| -> (&'a [V], &'a [U]) {
        (self.0.as_ref(), self.1.as_ref())
    }
);
impl_convert!(for ('a, V, U)
    |self: (&'a mut TiSlice<Id, V>, &'a mut TiSlice<Id, U>)| -> (&'a mut [V], &'a mut [U]) {
        (self.0.as_mut(), self.1.as_mut())
    }
);

impl_convert!(for ('a, V, U, W)
    |self: (&'a TiSlice<Id, V>, &'a TiSlice<Id, U>, &'a TiSlice<Id, W>)|
        -> (&'a [V], &'a [U], &'a [W])
    {
        (self.0.as_ref(), self.1.as_ref(), self.2.as_ref())
    }
);
impl_convert!(for ('a, V, U, W) |
    self: (&'a mut TiSlice<Id, V>, &'a mut TiSlice<Id, U>, &'a mut TiSlice<Id, W>
)| -> (&'a mut [V], &'a mut [U], &'a mut [W]) {
        (self.0.as_mut(), self.1.as_mut(), self.2.as_mut())
    }
);

impl_convert!(for (T) |self: Option<T>| -> Option<T::Target> where (T: TypedConvert) {
    self.map(|value| value.into_t())
});

impl_convert!(for (T, U) |self: Result<T, U>| -> Result<T::Target, U::Target>
    where (T: TypedConvert, U: TypedConvert) {
        self.map(|value| value.into_t()).map_err(|value| value.into_t())
    }
);

macro_rules! for_in {
    (for $name:ident in [$($value:expr),* $(,)?] $expr:expr) => {
        $({
            let $name = $value;
            $expr
        })*
    };
}

macro_rules! assert_api_impl(
    ( ($fn:ident) ($expr:expr) {$($common_init:tt)*} {$($lhs_init:tt)*} {$($rhs_init:tt)*} ) => {{
        $($common_init)*
        $fn!({
            #[deny(unused_imports)]
            use crate::test::TypedConvert;
            #[allow(dead_code, unused_qualifications)]
            type UsizeSlice = crate::TiSlice<Id, usize>;
            #[cfg(any(feature = "alloc", feature = "std"))]
            #[allow(dead_code, unused_qualifications)]
            type UsizeVec = crate::TiVec<Id, usize>;
            $($lhs_init)*
            $expr
        }, {
            #[deny(unused_imports)]
            use crate::test::DummyConvert;
            #[allow(dead_code, unused_qualifications)]
            type UsizeSlice = [usize];
            #[cfg(any(feature = "alloc", feature = "std"))]
            #[allow(dead_code, unused_qualifications)]
            type UsizeVec = alloc::vec::Vec<usize>;
            $($rhs_init)*
            $expr
        },
        "where expr: {}", stringify!($expr))
    }};
    (
        ($fn:ident) ($expr:expr) ($($mut_outer:tt)*) ($($mut_inner:tt)*)
        ($($ref:tt)*) ($source:expr) ($arg:ident)
    ) => {
        assert_api_impl!(($fn)($expr)
            {
                let $($mut_outer)* _1 = $source;
                let $($mut_outer)* _2 = $source;
            }
            { let $($mut_inner)* $arg = $($ref)* _1; }
            { let $($mut_inner)* $arg = $($ref)* _2; }
        );
    };
    (($fn:ident)($expr:expr)) => {
        assert_api_impl!(($fn)($expr){}{}{});
    };
);

macro_rules! assert_eq_api(
    ($expr:expr) => { assert_api_impl!((assert_eq)($expr)) };
    ($source:expr => |&mut $arg:ident| $expr:expr) => {
        assert_api_impl!((assert_eq)($expr)(mut)()(&mut)($source)($arg))
    };
    ($source:expr => |mut $arg:ident| $expr:expr) => {
        assert_api_impl!((assert_eq)($expr)()(mut)()($source)($arg))
    };
    ($source:expr => |&$arg:ident| $expr:expr) => {
        assert_api_impl!((assert_eq)($expr)()()(&)($source)($arg))
    };
    ($source:expr => |$arg:ident| $expr:expr) => {
        assert_api_impl!((assert_eq)($expr)()()()($source)($arg))
    };
);

macro_rules! assert_ne_api(
    ($expr:expr) => { assert_api_impl!((assert_eq)($expr)) };
    ($source:expr => |&mut $arg:ident| $expr:expr) => {
        assert_api_impl!((assert_ne)($expr)(mut)()(&mut)($source)($arg))
    };
    ($source:expr => |mut $arg:ident| $expr:expr) => {
        assert_api_impl!((assert_ne)($expr)()(mut)()($source)($arg))
    };
    ($source:expr => |&$arg:ident| $expr:expr) => {
        assert_api_impl!((assert_ne)($expr)()()(&)($source)($arg))
    };
    ($source:expr => |$arg:ident| $expr:expr) => {
        assert_api_impl!((assert_ne)($expr)()()()($source)($arg))
    };
);
