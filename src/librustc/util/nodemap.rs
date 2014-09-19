// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! An efficient hash map for node IDs

#![allow(non_snake_case)]

use std::collections::{HashMap, HashSet};
use std::hash::{Hasher, Hash, Writer};
use syntax::ast;

pub type FnvHashMap<K, V> = HashMap<K, V>;
pub type FnvHashSet<V> = HashSet<V>;

pub type NodeMap<T> = FnvHashMap<ast::NodeId, T>;
pub type DefIdMap<T> = FnvHashMap<ast::DefId, T>;

pub type NodeSet = FnvHashSet<ast::NodeId>;
pub type DefIdSet = FnvHashSet<ast::DefId>;

// Hacks to get good names
pub mod FnvHashMap {
    use std::hash::Hash;
    use std::collections::HashMap;
    pub fn new<K: Hash + Eq, V>() -> super::FnvHashMap<K, V> {
        HashMap::new()
    }
}
pub mod FnvHashSet {
    use std::hash::Hash;
    use std::collections::HashSet;
    pub fn new<V: Hash + Eq>() -> super::FnvHashSet<V> {
        HashSet::new()
    }
}
pub mod NodeMap {
    pub fn new<T>() -> super::NodeMap<T> {
        super::FnvHashMap::new()
    }
}
pub mod DefIdMap {
    pub fn new<T>() -> super::DefIdMap<T> {
        super::FnvHashMap::new()
    }
}
pub mod NodeSet {
    pub fn new() -> super::NodeSet {
        super::FnvHashSet::new()
    }
}
pub mod DefIdSet {
    pub fn new() -> super::DefIdSet {
        super::FnvHashSet::new()
    }
}
