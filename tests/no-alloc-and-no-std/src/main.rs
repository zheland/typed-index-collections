#![no_std]
#![no_main]
#![allow(
    dead_code,
    missing_docs,
    clippy::empty_loop,
    clippy::missing_panics_doc,
    clippy::panic,
    clippy::undocumented_unsafe_blocks,
    clippy::unimplemented,
    reason = "okay in tests"
)]

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "global-allocator")]
use core::alloc::{GlobalAlloc, Layout};
#[cfg(feature = "panic-handler")]
use core::panic::PanicInfo;

#[cfg(feature = "global-allocator")]
struct DummyAllocator;

#[cfg(feature = "global-allocator")]
#[global_allocator]
static GLOBAL_ALLOCATOR: DummyAllocator = DummyAllocator;

#[cfg(feature = "panic-handler")]
#[panic_handler]
const fn panic(_: &PanicInfo<'_>) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub const extern "C" fn _start() -> ! {
    loop {}
}

#[cfg(feature = "global-allocator")]
unsafe impl GlobalAlloc for DummyAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        unimplemented!()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        unimplemented!()
    }
}

#[unsafe(no_mangle)]
pub const extern "C" fn test_core() {
    use typed_index_collections::TiSlice;
    struct K(usize);
    let slice = &[1, 2, 3];
    let ti_slice: &TiSlice<K, usize> = TiSlice::from_ref(slice);
    let _ = ti_slice;
}

#[cfg(feature = "alloc")]
#[unsafe(no_mangle)]
pub extern "C" fn test_alloc() {
    use typed_index_collections::TiVec;

    struct K(usize);
    let mut ti_vec: TiVec<K, usize> = TiVec::new();
    ti_vec.extend([1, 2, 3]);
    drop(ti_vec);
}

#[cfg(feature = "std")]
#[unsafe(no_mangle)]
pub extern "C" fn test_std() {
    use std::io::Write;
    use typed_index_collections::TiVec;

    struct K(usize);
    let mut ti_vec: TiVec<K, u8> = TiVec::new();
    let _res = ti_vec.write_all(&[4, 5, 6]);
    drop(ti_vec);
}
