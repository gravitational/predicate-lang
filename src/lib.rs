use std::ffi::{CStr, CString};
use std::mem;
use std::os::raw::c_void;

#[no_mangle]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    a + b
}

// In order to work with the memory we expose (de)allocation methods
#[no_mangle]
pub extern "C" fn alloc(size: usize) -> *mut c_void {
    let mut buf = Vec::with_capacity(size);
    let ptr = buf.as_mut_ptr();
    mem::forget(buf);
    return ptr as *mut c_void;
}

#[no_mangle]
pub extern "C" fn dealloc(ptr: *mut c_void, cap: usize) {
    unsafe {
        let _buf = Vec::from_raw_parts(ptr, 0, cap);
    }
}

#[no_mangle]
pub extern "C" fn set_at(ptr: *mut c_void, offset: i32, val: i32) {
    unsafe {
        let uptr = ptr as *mut u8;
        *uptr.offset(offset as isize) = val as u8;
    }
}

#[no_mangle]
pub extern "C" fn get_at(ptr: *mut c_void, offset: i32) -> i32 {
    unsafe {
        let uptr = ptr as *mut u8;
        *uptr.offset(offset as isize) as i32
    }
}

#[no_mangle]
pub extern "C" fn log(data: *mut c_void, len: u32) -> u32 {
    let bytes: Vec<u8> =
        unsafe { Vec::from_raw_parts(data as *mut u8, len as usize, len as usize) };

    for byte in bytes.iter() {
        println!("byte: {}", byte);
    }
    0
}
