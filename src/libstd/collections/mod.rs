// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Collection types.
 */

#![feature(macro_rules, globs, asm, managed_boxes, thread_local, link_args,
           linkage, default_type_params, phase, concat_idents, quad_precision_float)]

#![allow(deprecated)]
#![deny(missing_doc)]

// When testing libstd, bring in libuv as the I/O backend so tests can print
// things and all of the std::io tests have an I/O interface to run on top
// of
#[cfg(test)] extern crate rustuv;
#[cfg(test)] extern crate native;
#[cfg(test)] extern crate green;
#[cfg(test)] extern crate debug;
#[cfg(test)] #[phase(syntax, link)] extern crate log;

extern crate alloc;
extern crate core;
extern crate libc;
extern crate core_rand = "rand";
extern crate core_collections = "collections";
extern crate std;

// Make std testable by not duplicating lang items. See #2912
#[cfg(test)] extern crate realstd = "std";
#[cfg(test)] pub use realstd::kinds;
#[cfg(test)] pub use realstd::ops;
#[cfg(test)] pub use realstd::cmp;
#[cfg(test)] pub use realstd::ty;


pub use std::{rand, fmt, num, prelude, rt};

// NB: These reexports are in the order they should be listed in rustdoc

pub use core::any;
pub use core::bool;
pub use core::cell;
pub use core::char;
pub use core::clone;
#[cfg(not(test))] pub use core::cmp;
pub use core::container;
pub use core::default;
pub use core::finally;
pub use core::intrinsics;
pub use core::iter;
#[cfg(not(test))] pub use core::kinds;
pub use core::mem;
#[cfg(not(test))] pub use core::ops;
pub use core::ptr;
pub use core::raw;
pub use core::simd;
pub use core::tuple;
#[cfg(not(test))] pub use core::ty;
pub use core::result;
pub use core::option;

pub use alloc::owned;
pub use alloc::rc;

pub use core_collections::hash;
pub use core_collections::slice;
pub use core_collections::str;
pub use core_collections::string;
pub use core_collections::vec;

pub use core_collections::{Collection, Mutable, Map, MutableMap};
pub use core_collections::{Bitv, BitvSet, BTree, Set, MutableSet, Deque, DList, EnumSet};
pub use core_collections::{PriorityQueue, RingBuf, SmallIntMap};
pub use core_collections::{TreeMap, TreeSet, TrieMap, TrieSet};
pub use core_collections::{bitv, btree, dlist, enum_set};
pub use core_collections::{priority_queue, ringbuf, smallintmap, treemap, trie};

pub use self::hashmap::{HashMap, HashSet};
// pub use self::lru_cache::LruCache;

pub mod hashmap;
// pub mod lru_cache;
