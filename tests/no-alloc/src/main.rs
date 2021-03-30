#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    #[allow(clippy::empty_loop)]
    loop {}
}

#[no_mangle]
pub extern "C" fn slice_test() {
    use typed_index_collections::TiSlice;
    struct K(usize);
    let slice = &[1, 2, 3];
    let ti_slice: &TiSlice<K, usize> = TiSlice::from_ref(slice);
    let _ = ti_slice;
}
