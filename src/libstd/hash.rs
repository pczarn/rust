// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Generic hashing support.
 *
 * This module provides a generic way to compute the hash of a value. The
 * simplest way to make a type hashable is to use `#[deriving(Hash)]`:
 *
 * # Example
 *
 * ```rust
 * use std::hash;
 * use std::hash::Hash;
 *
 * #[deriving(Hash)]
 * struct Person {
 *     id: uint,
 *     name: String,
 *     phone: u64,
 * }
 *
 * let person1 = Person { id: 5, name: "Janet".to_string(), phone: 555_666_7777 };
 * let person2 = Person { id: 5, name: "Bob".to_string(), phone: 555_666_7777 };
 *
 * assert!(hash::hash(&person1) != hash::hash(&person2));
 * ```
 *
 * If you need more control over how a value is hashed, you need to implement
 * the trait `Hash`:
 *
 * ```rust
 * use std::hash;
 * use std::hash::Hash;
 * use std::hash::sip::SipState;
 *
 * struct Person {
 *     id: uint,
 *     name: String,
 *     phone: u64,
 * }
 *
 * impl Hash for Person {
 *     fn hash(&self, state: &mut SipState) {
 *         self.id.hash(state);
 *         self.phone.hash(state);
 *     }
 * }
 *
 * let person1 = Person { id: 5, name: "Janet".to_string(), phone: 555_666_7777 };
 * let person2 = Person { id: 5, name: "Bob".to_string(), phone: 555_666_7777 };
 *
 * assert!(hash::hash(&person1) == hash::hash(&person2));
 * ```
 */

#![experimental]

pub use core_collections::hash::{Hash, Hasher, Writer, hash, sip, xxh};

use default::Default;
use mem;
use rand::Rng;
use rand;

/// `RandomSipHasher` computes the SipHash algorithm from a stream of bytes
/// initialized with random keys.
#[deriving(Clone)]
pub struct RandomSipHasher {
    hasher: sip::SipHasher,
}

impl RandomSipHasher {
    /// Construct a new `RandomSipHasher` that is initialized with random keys.
    #[inline]
    pub fn new() -> RandomSipHasher {
        let mut r = rand::task_rng();
        let r0 = r.gen();
        let r1 = r.gen();
        RandomSipHasher {
            hasher: sip::SipHasher::new_with_keys(r0, r1),
        }
    }
}

impl Hasher<sip::SipState> for RandomSipHasher {
    #[inline]
    fn hash<T: Hash<sip::SipState>>(&self, value: &T) -> u64 {
        self.hasher.hash(value)
    }
}

impl Default for RandomSipHasher {
    #[inline]
    fn default() -> RandomSipHasher {
        RandomSipHasher::new()
    }
}

#[deriving(Clone)]
struct XxHashOrRandomSipHasher {
    hasher: sip::SipHasher,
}

impl XxHashOrRandomSipHasher {
    /// Construct a new `XxHashOrRandomSipHasher` that initially uses xxhash.
    #[inline]
    pub fn new() -> XxHashOrRandomSipHasher {
        XxHashOrRandomSipHasher {
            hasher: sip::SipHasher::new_with_keys(0, 0),
        }
    }
}
// Hasher<SipState> + Hasher<XxState>
impl<W: Writer> Hasher<W> for XxHashOrRandomSipHasher {
    #[inline]
    fn hash<T: Hash<W>>(&self, value: &T) -> u64 {
        let copy: u32 = unsafe {
            mem::transmute_copy(self)
        };
        if copy == 0 {
            xxh::XxHasher64::new().hash(value)
        } else {
            self.hasher.hash(value)
        }
    }
//hash.rs:129:13: 129:47 error: expected collections::hash::Hash<collections::hash::xxh::XxState64>, found collections::hash::Hash (expected struct collections::hash::xxh::XxState64, found struct collections::hash::sip::SipState) [E0095]
//hash.rs:129             xxh::XxHasher64::new().hash(value)
//                        ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    fn reset(&mut self) {
        let mut r = rand::task_rng();
        let r0 = r.gen();
        let r1 = r.gen();
        self.hasher = sip::SipHasher::new_with_keys(r0, r1);
    }
}

impl Default for XxHashOrRandomSipHasher {
    #[inline]
    fn default() -> XxHashOrRandomSipHasher {
        XxHashOrRandomSipHasher::new()
    }
}
