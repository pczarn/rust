// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::prelude::*;

use core::default::Default;
use core::mem;
use core::ptr;
use core::slice::bytes::copy_memory;

use super::{Hash, Hasher, Writer};


static PRIME1: u32 = 2654435761;
static PRIME2: u32 = 2246822519;
static PRIME3: u32 = 3266489917;
static PRIME4: u32 = 668265263;
static PRIME5: u32 = 374761393;

static PRIME64_1: u64 = 11400714785074694791;
static PRIME64_2: u64 = 14029467366897019727;
static PRIME64_3: u64 =  1609587929392839161;
static PRIME64_4: u64 =  9650029242287828579;
static PRIME64_5: u64 =  2870177450012600261;

macro_rules! rotl32 (
    ($x:expr, $b:expr) =>
    (($x << $b) | ($x >> (32 - $b)))
)

macro_rules! rotl64 (
    ($x:expr, $b:expr) =>
    (($x << $b) | ($x >> (64 - $b)))
)

// sadly, these macro definitions can't appear later,
// because they're needed in the following defs;
// this design could be improved.

// macro_rules! u8to64_le (
//     ($buf:expr, $i:expr) =>
//     ($buf[0+$i] as u64 |
//      $buf[1+$i] as u64 << 8 |
//      $buf[2+$i] as u64 << 16 |
//      $buf[3+$i] as u64 << 24 |
//      $buf[4+$i] as u64 << 32 |
//      $buf[5+$i] as u64 << 40 |
//      $buf[6+$i] as u64 << 48 |
//      $buf[7+$i] as u64 << 56);
//     ($buf:expr, $i:expr, $len:expr) =>
//     ({
//         let mut t = 0;
//         let mut out = 0u64;
//         while t < $len {
//             out |= $buf[t+$i] as u64 << t*8;
//             t += 1;
//         }
//         out
//     });
// )

macro_rules! u8to32_le (
    ($buf:expr, $i:expr) =>
    ($buf[0+$i] as u32 |
     $buf[1+$i] as u32 << 8 |
     $buf[2+$i] as u32 << 16 |
     $buf[3+$i] as u32 << 24);
    ($buf:expr, $i:expr, $len:expr) =>
    ({
        let mut t = 0;
        let mut out = 0u32;
        while t < $len {
            out |= $buf[t+$i] as u64 << t*8;
            t += 1;
        }
        out
    });
)

#[inline(always)]
pub fn u8to64_le(data: &[u8], start: uint) -> u64 {
    use core::ptr::copy_nonoverlapping_memory;
    use core::num::Int;
    use core::slice::MutableSlice;

    let mut buf = [0u8, ..8];
    unsafe {
        let ptr = data.slice(start, start + 8).as_ptr();
        let out = buf.as_mut_ptr();
        copy_nonoverlapping_memory(out, ptr, 8);
        Int::from_le(*(out as *const u64))
    }
}

pub struct XxState32 {
    // field names match the C implementation
    memory: [u8, ..16],
    total_len: u64,
    v1: u32,
    v2: u32,
    v3: u32,
    v4: u32,
    memsize: uint,
    seed: u32,
}

impl XxState32 {
    #[inline]
    pub fn new(seed: u32) -> XxState32 {
        // no need to write it twice
        let mut xxh: XxState32 = unsafe { mem::uninitialized() };
        xxh.reset(seed);
        xxh
    }

    #[inline]
    pub fn reset(&mut self, seed: u32) {
        self.seed = seed;
        self.v1 = seed + PRIME1 + PRIME2;
        self.v2 = seed + PRIME2;
        self.v3 = seed;
        self.v4 = seed - PRIME1;
        self.total_len = 0;
        self.memsize = 0;
    }

    #[inline]
    fn result(&self) -> u32 {
        let mut p = 0;

        let mut h32: u32 = match self.total_len >= 16 {
            true => rotl32!(self.v1, 1) + rotl32!(self.v2, 7) + rotl32!(self.v3, 12) + rotl32!(self.v4, 18),
            false => self.seed + PRIME5
        };

        h32 += self.total_len as u32;

        let rem = (self.total_len & 15) / 4;
        for _ in range (0, rem) {
            h32 += u8to32_le!(self.memory, p) * PRIME3;
            h32 = rotl32!(h32, 17) * PRIME4;
            p += 4;
        }

        let rem = self.total_len & 3;
        for _ in range(0, rem) {
            h32 += self.memory[p] as u32 * PRIME5;
            h32 = rotl32!(h32, 11) * PRIME1;
            p += 1;
        }

        h32 ^= h32 >> 15;
        h32 *= PRIME2;
        h32 ^= h32 >> 13;
        h32 *= PRIME3;
        h32 ^= h32 >> 16;

        h32
    }
}

impl Writer for XxState32 {
    #[inline]
    fn write(&mut self, msg: &[u8]) {unsafe{
        let mut len = msg.len();
        let mut data = msg.as_ptr();

        self.total_len += len as u64;

        if self.memsize + len < 16 {
            // not enough data for one 16-byte chunk, so just fill the buffer and return.
            let dst: *mut u8 = (&mut self.memory[0] as *mut u8).offset(self.memsize as int);
            ptr::copy_nonoverlapping_memory(dst, data, len as uint);
            self.memsize += len;
            return;
        }

        if self.memsize != 0 {
            // some data left from previous update
            // fill the buffer and eat it
            let dst: *mut u8 = (&mut self.memory[0] as *mut u8).offset(self.memsize as int);
            let bump = 16 - self.memsize;
            ptr::copy_nonoverlapping_memory(dst, data, bump as uint);

            let mut p = &self.memory as *const _ as *const u32;

            let mut v1: u32 = self.v1;
            let mut v2: u32 = self.v2;
            let mut v3: u32 = self.v3;
            let mut v4: u32 = self.v4;

            v1 += (*p) * PRIME2; v1 = rotl32!(v1, 13); v1 *= PRIME1; p = p.offset(1);
            v2 += (*p) * PRIME2; v2 = rotl32!(v2, 13); v2 *= PRIME1; p = p.offset(1);
            v3 += (*p) * PRIME2; v3 = rotl32!(v3, 13); v3 *= PRIME1; p = p.offset(1);
            v4 += (*p) * PRIME2; v4 = rotl32!(v4, 13); v4 *= PRIME1;

            self.v1 = v1;
            self.v2 = v2;
            self.v3 = v3;
            self.v4 = v4;

            data = data.offset(bump as int);
            len -= bump;
            self.memsize = 0;

        }

        let mut p: *const u32 = mem::transmute(data);
        let chunks = len >> 4;
        let rem = len & 15;

        let mut v1: u32 = self.v1;
        let mut v2: u32 = self.v2;
        let mut v3: u32 = self.v3;
        let mut v4: u32 = self.v4;

        for _ in range(0, chunks) {
            v1 += (*p) * PRIME2; v1 = rotl32!(v1, 13); v1 *= PRIME1; p = p.offset(1);
            v2 += (*p) * PRIME2; v2 = rotl32!(v2, 13); v2 *= PRIME1; p = p.offset(1);
            v3 += (*p) * PRIME2; v3 = rotl32!(v3, 13); v3 *= PRIME1; p = p.offset(1);
            v4 += (*p) * PRIME2; v4 = rotl32!(v4, 13); v4 *= PRIME1; p = p.offset(1);
        }

        self.v1 = v1;
        self.v2 = v2;
        self.v3 = v3;
        self.v4 = v4;

        if rem > 0 {
            let dst: *mut u8 = &mut self.memory[0] as *mut u8;
            ptr::copy_nonoverlapping_memory(dst, data, rem);
            self.memsize = rem;
        }
    }}
}

impl Clone for XxState32 {
    #[inline]
    fn clone(&self) -> XxState32 {
        *self
    }
}

impl Default for XxState32 {
    #[inline]
    fn default() -> XxState32 {
        XxState32::new(0)
    }
}

pub struct XxHasher32 {
    seed: u32
}

impl XxHasher32 {
    pub fn new() -> XxHasher32 { #![inline]
        XxHasher32::new_with_seed(0)
    }

    pub fn new_with_seed(seed: u32) -> XxHasher32 { #![inline]
        XxHasher32 { seed: seed }
    }
}

impl Hasher<XxState32> for XxHasher32 {
    fn hash<T: Hash<XxState32>>(&self, value: &T) -> u64 {
        let mut state = XxState32::new(self.seed);
        value.hash(&mut state);
        state.result() as u64
    }
}

pub fn hash<T: Hash<XxState32>>(value: &T) -> u32 {
    let mut state = XxState32::new(0);
    value.hash(&mut state);
    state.result()
}

pub fn hash_with_seed<T: Hash<XxState32>>(seed: u32, value: &T) -> u32 {
    let mut state = XxState32::new(seed);
    value.hash(&mut state);
    state.result()
}

pub struct XxState64 {
    memory: [u8, ..32],
    total_len: u64,
    v1: u64,
    v2: u64,
    v3: u64,
    v4: u64,
    memsize: uint,
    seed: u64,
}

impl XxState64 {
    #[inline]
    pub fn new(seed: u64) -> XxState64 {
        // no need to write it twice
        let mut xxh: XxState64 = unsafe { mem::uninitialized() };
        xxh.reset(seed);
        xxh
    }

    #[inline]
    pub fn reset(&mut self, seed: u64) {
        self.seed = seed;
        self.v1 = seed + PRIME64_1 + PRIME64_2;
        self.v2 = seed + PRIME64_2;
        self.v3 = seed;
        self.v4 = seed - PRIME64_1;
        self.total_len = 0;
        self.memsize = 0;
    }

    #[inline]
    pub fn result(&self) -> u64 {unsafe{ 
        let mut p = &self.memory as *const _ as *const u64;

        let mut h64 = match self.total_len {
            0..31 => self.seed + PRIME64_5,
            _ => {
                let mut v1: u64 = self.v1;
                let mut v2: u64 = self.v2;
                let mut v3: u64 = self.v3;
                let mut v4: u64 = self.v4;

                let mut h64 = rotl64!(v1, 1) + rotl64!(v2, 7) + rotl64!(v3, 12) + rotl64!(v4, 18);

                v1 *= PRIME64_2; v1 = rotl64!(v1, 31); v1 *= PRIME64_1;
                v2 *= PRIME64_2; v2 = rotl64!(v2, 31); v2 *= PRIME64_1;
                v3 *= PRIME64_2; v3 = rotl64!(v3, 31); v3 *= PRIME64_1;
                v4 *= PRIME64_2; v4 = rotl64!(v4, 31); v4 *= PRIME64_1;
                h64 ^= v1; h64 = h64 * PRIME64_1 + PRIME64_4;
                h64 ^= v2; h64 = h64 * PRIME64_1 + PRIME64_4;
                h64 ^= v3; h64 = h64 * PRIME64_1 + PRIME64_4;
                h64 ^= v4; h64 = h64 * PRIME64_1 + PRIME64_4;

                h64
            }
        };

        h64 += self.total_len as u64;

        let rem = (self.total_len & 31) / 8;
        for _ in range(0, rem) {
            let mut k1: u64 = *p;
            k1 *= PRIME64_2;
            k1 = rotl64!(k1, 31);
            k1 *= PRIME64_1;
            h64 ^= k1;
            h64 = rotl64!(h64, 27) * PRIME64_1 + PRIME64_4;
            p = p.offset(1);
        }

        let mut dwp = p as *const u32;
        if self.total_len & 4 == 4 {
            h64 ^= *dwp as u64 * PRIME64_1;
            h64 = rotl64!(h64, 23) * PRIME64_2 + PRIME64_3;
            dwp = dwp.offset(1);
        }

        let rem = self.total_len & 3;
        let mut bp = dwp as *const u8;
        for _ in range(0, rem) {
            h64 ^= *(bp) as u64 * PRIME64_5;
            h64 = rotl64!(h64, 11) * PRIME64_1;
            bp = bp.offset(1);
        }

        h64 ^= h64 >> 33;
        h64 *= PRIME64_2;
        h64 ^= h64 >> 29;
        h64 *= PRIME64_3;
        h64 ^= h64 >> 32;

        h64
    }}
}

impl Writer for XxState64 {
    #[inline]
    fn write(&mut self, mut msg: &[u8]) {
        let len = msg.len();

        self.total_len += len as u64;

        if self.memsize + len < 32 {
            // not enough data for one 32-byte chunk, so just fill the buffer and return.
            copy_memory(self.memory.slice_from_mut(self.memsize), msg);
            self.memsize += len;
            return;
        }

        // let mut i = 0;

        if self.memsize != 0 {
            // some data left from previous update
            // fill the buffer and eat it
            let pos = 32 - self.memsize;
            let (head, _msg) = msg.split_at(pos);
            msg = _msg;
            copy_memory(self.memory.slice_from_mut(self.memsize), head);

            let mut v1: u64 = self.v1;
            let mut v2: u64 = self.v2;
            let mut v3: u64 = self.v3;
            let mut v4: u64 = self.v4;

            v1 += u8to64_le(self.memory,  0) * PRIME64_2; v1 = rotl64!(v1, 31); v1 *= PRIME64_1;
            v2 += u8to64_le(self.memory,  8) * PRIME64_2; v2 = rotl64!(v2, 31); v2 *= PRIME64_1;
            v3 += u8to64_le(self.memory, 16) * PRIME64_2; v3 = rotl64!(v3, 31); v3 *= PRIME64_1;
            v4 += u8to64_le(self.memory, 24) * PRIME64_2; v4 = rotl64!(v4, 31); v4 *= PRIME64_1;

            self.v1 = v1;
            self.v2 = v2;
            self.v3 = v3;
            self.v4 = v4;
        }

        let end = msg.len() & !31;
        let left = msg.len() & 31;

        let mut v1: u64 = self.v1;
        let mut v2: u64 = self.v2;
        let mut v3: u64 = self.v3;
        let mut v4: u64 = self.v4;

        let (msg, rest) = msg.split_at(end);
        for chunk in msg.chunks(32) {
            let p1 = u8to64_le(chunk, 0);
            let p2 = u8to64_le(chunk, 8);
            let p3 = u8to64_le(chunk, 16);
            let p4 = u8to64_le(chunk, 24);

            v1 += p1 * PRIME64_2; v1 = rotl64!(v1, 31); v1 *= PRIME64_1;
            v2 += p2 * PRIME64_2; v2 = rotl64!(v2, 31); v2 *= PRIME64_1;
            v3 += p3 * PRIME64_2; v3 = rotl64!(v3, 31); v3 *= PRIME64_1;
            v4 += p4 * PRIME64_2; v4 = rotl64!(v4, 31); v4 *= PRIME64_1;
        }

        self.v1 = v1;
        self.v2 = v2;
        self.v3 = v3;
        self.v4 = v4;

        if left > 0 {
            copy_memory(self.memory, rest);
        }
        self.memsize = left;
    }
}

impl Clone for XxState64 {
    #[inline]
    fn clone(&self) -> XxState64 {
        *self
    }
}

impl Default for XxState64 {
    #[inline]
    fn default() -> XxState64 {
        XxState64::new(0)
    }
}

pub struct XxHasher64 {
    seed: u64
}

impl XxHasher64 {
    #[inline]
    pub fn new() -> XxHasher64 {
        XxHasher64::new_with_seed(0)
    }

    #[inline]
    pub fn new_with_seed(seed: u64) -> XxHasher64 {
        XxHasher64 { seed: seed }
    }
}

impl Hasher<XxState64> for XxHasher64 {
    fn hash<T: Hash<XxState64>>(&self, value: &T) -> u64 {
        let mut state = XxState64::new(self.seed);
        value.hash(&mut state);
        state.result()
    }
}
