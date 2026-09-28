#[cfg(feature = "nightly")]
pub use alloc::alloc::{Allocator, Global};

// Dummy allocator, not exposed outside of this crate.
#[cfg(not(feature = "nightly"))]
pub trait Allocator {}

// Dummy global allocator, not exposed outside of this crate.
#[cfg(not(feature = "nightly"))]
#[derive(Copy, Clone, Default, Debug)]
pub struct Global;

#[cfg(not(feature = "nightly"))]
impl Allocator for Global {}
