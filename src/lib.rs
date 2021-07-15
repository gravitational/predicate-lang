mod hello;

use hello::{Request, Response, ResponseHeader};
use protobuf::Message;
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
pub extern "C" fn call(
    req: *mut c_void,
    req_len: u32,
    resp_header: *mut c_void,
    resp_header_len: u32,
) -> u32 {
    let req_bytes: Vec<u8> =
        unsafe { Vec::from_raw_parts(req as *mut u8, req_len as usize, req_len as usize) };

    let req: Request = Message::parse_from_bytes(&req_bytes).unwrap();

    let resp_header_bytes: Vec<u8> = unsafe {
        Vec::from_raw_parts(
            resp_header as *mut u8,
            resp_header_len as usize,
            resp_header_len as usize,
        )
    };

    let mut resp_header: ResponseHeader = Message::parse_from_bytes(&resp_header_bytes).unwrap();

    let mut re = Response::new();
    re.set_Message(req.get_Message().to_string());

    resp_header.SizeBytes = re.compute_size();
    let mut response_bytes = Message::write_to_bytes(&re).unwrap();

    let response_ptr = response_bytes.as_mut_ptr();
    mem::forget(response_bytes);
    resp_header.Ptr = response_ptr as u32;
    0
}
