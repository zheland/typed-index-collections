// `Allocator` moved to `core` in Rust 1.100.0.
// `core_or_alloc` re-export is a workaround for Clippy, since warning
// suppression doesn't work here for some reason.
#[cfg(feature = "nightly")]
use alloc as core_or_alloc;
#[cfg(feature = "nightly")]
pub use alloc::alloc::Global;

#[cfg(feature = "nightly")]
pub use core_or_alloc::alloc::Allocator;

// Dummy allocator, not exposed outside of this crate.
#[cfg(not(feature = "nightly"))]
pub trait Allocator {}

// Dummy global allocator, not exposed outside of this crate.
#[cfg(not(feature = "nightly"))]
#[derive(Copy, Clone, Default, Debug)]
pub struct Global;

#[cfg(not(feature = "nightly"))]
impl Allocator for Global {}
