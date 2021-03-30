#![feature(default_alloc_error_handler)]
#![no_std]
#![no_main]

extern crate alloc;

use core::alloc::{GlobalAlloc, Layout};
use core::panic::PanicInfo;
use core::ptr::null_mut;

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    #[allow(clippy::empty_loop)]
    loop {}
}

struct DummyAllocator;

unsafe impl GlobalAlloc for DummyAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        null_mut()
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static GLOBAL_ALLOCATOR: DummyAllocator = DummyAllocator;

#[no_mangle]
pub extern "C" fn vec_test() {
    use typed_index_collections::TiVec;
    struct K(usize);
    let vec = alloc::vec![1, 2, 3];
    let ti_vec: TiVec<K, usize> = TiVec::from(vec);
    let _ = ti_vec;
}
