// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Unordered containers, implemented as hash-tables (`HashSet` and `HashMap` types)

use clone::Clone;
use cmp::{max, Eq, Equiv, PartialEq};
use collections::{Collection, Mutable, Set, MutableSet, Map, MutableMap};
use default::Default;
use fmt::Show;
use fmt;
use hash::{Hash, Hasher, sip};
use iter::{Iterator, FromIterator, FilterMap, Chain, Repeat, Zip, Extendable, Cycle};
use iter::{range, range_inclusive, range_step_inclusive, FromIterator, CloneableIterator};
use iter;
use slice::MutableVector;
use mem::replace;
use num;
use option::{Some, None, Option};
use rand::Rng;
use rand;
use result::{Ok, Err};
use kinds::marker;
use mem::overwrite;
use ptr;
// use core::num::Bitwise;

use vec::Vec;
use slice::ImmutableVector;
mod table {
    use clone::Clone;
    use cmp;
    use hash::{Hash, Hasher};
    use iter::range_step_inclusive;
    use iter::{Iterator, range};
    use kinds::marker;
    use mem::{min_align_of, size_of};
    use mem::{overwrite, transmute};
    use num::{CheckedMul, is_power_of_two};
    use ops::Drop;
    use option::{Some, None, Option};
    use ptr::RawPtr;
    use ptr::set_memory;
    use ptr;
    // use rt::heap::{allocate, deallocate};
    use tuple::{Tuple3, Tuple8};
    use collections::Collection;
    use vec::Vec;
    use iter::{Iterator, CloneableIterator};
    use iter::{range_step_inclusive, range_step};
    use iter::{RangeStepInclusive, Zip, Skip, Cycle, Chain, RangeStep, Range, FlatMap};
    use slice::{MutItems, MutableVector};
    use alloc::heap::{reallocate_inplace, deallocate, reallocate, allocate, stats_print};
    use mem;
    use core::raw::Slice;

    static EMPTY_BUCKET: u64 = 0u64;

    /// The raw hashtable, providing safe-ish access to the unzipped and highly
    /// optimized arrays of hashes, keys, and values.
    ///
    /// This design uses less memory and is a lot faster than the naive
    /// `Vec<Option<u64, K, V>>`, because we don't pay for the overhead of an
    /// option on every element, and we get a generally more cache-aware design.
    ///
    /// Key invariants of this structure:
    ///
    ///   - if hashes[i] == EMPTY_BUCKET, then keys[i] and vals[i] have
    ///     'undefined' contents. Don't read from them. This invariant is
    ///     enforced outside this module with the `EmptyIndex`, `FullIndex`,
    ///     and `SafeHash` types.
    ///
    ///   - An `EmptyIndex` is only constructed for a bucket at an index with
    ///     a hash of EMPTY_BUCKET.
    ///
    ///   - A `FullIndex` is only constructed for a bucket at an index with a
    ///     non-EMPTY_BUCKET hash.
    ///
    ///   - A `SafeHash` is only constructed for non-`EMPTY_BUCKET` hash. We get
    ///     around hashes of zero by changing them to 0x8000_0000_0000_0000,
    ///     which will likely map to the same bucket, while not being confused
    ///     with "empty".
    ///
    ///   - All three "arrays represented by pointers" are the same length:
    ///     `capacity`. This is set at creation and never changes. The arrays
    ///     are unzipped to save space (we don't have to pay for the padding
    ///     between odd sized elements, such as in a map from u64 to u8), and
    ///     be more cache aware (scanning through 8 hashes brings in 2 cache
    ///     lines, since they're all right beside each other).
    ///
    /// You can kind of think of this module/data structure as a safe wrapper
    /// around just the "table" part of the hashtable. It enforces some
    /// invariants at the type level and employs some performance trickery,
    /// but in general is just a tricked out `Vec<Option<u64, K, V>>`.
    ///
    /// FIXME(cgaebel):
    ///
    /// Feb 11, 2014: This hashtable was just implemented, and, hard as I tried,
    /// isn't yet totally safe. There's a "known exploit" that you can create
    /// multiple FullIndexes for a bucket, `take` one, and then still `take`
    /// the other causing undefined behavior. Currently, there's no story
    /// for how to protect against this statically. Therefore, there are asserts
    /// on `take`, `get`, `get_mut`, and `put` which check the bucket state.
    /// With time, and when we're confident this works correctly, they should
    /// be removed. Also, the bounds check in `peek` is especially painful,
    /// as that's called in the innermost loops of the hashtable and has the
    /// potential to be a major performance drain. Remove this too.
    ///
    /// Or, better than remove, only enable these checks for debug builds.
    /// There's currently no "debug-only" asserts in rust, so if you're reading
    /// this and going "what? of course there are debug-only asserts!", then
    /// please make this use them!

    // A fixed length tri-vec.
    // An array length of 8 (= 2^3) is enough to ensure good cache locality
    // in hashmaps for which `size_of<K> + size_of<V>` is a multiple of 8,
    // on systems with cache line of 64 bytes of smaller.
    pub static LOG2_CHUNK: uint = 4;
    pub static CHUNK: uint = 1 << LOG2_CHUNK; // 8 or 16 or 32
    pub static CHUNK_MASK: uint = CHUNK - 1;

    pub type TriAry<K, V> = (
        [u64, ..CHUNK],
        [ K , ..CHUNK],
        [ V , ..CHUNK]
    );

    #[unsafe_no_drop_flag]
    pub struct RawTable<K, V> {
        // rm pub
        pub len: uint,
        pub cap: uint,
        pub ptr: *mut TriAry<K, V>
    }

    /// Represents an index into a `RawTable` with no key or value in it.
    pub struct EmptyIndex {
        pub idx:    int,
        nocopy: marker::NoCopy,
    }

    /// Represents an index into a `RawTable` with a key, value, and hash
    /// in it.
    pub struct FullIndex {
        pub idx:    int,
        pub hash:   SafeHash,
        pub nocopy: marker::NoCopy,
    }

    impl FullIndex {
        /// Since we get the hash for free whenever we check the bucket state,
        /// this function is provided for fast access, letting us avoid
        /// redundant trips back to the hashtable.
        #[inline(always)]
        pub fn hash(&self) -> SafeHash { self.hash }

        /// Same comment as with `hash`.
        #[inline(always)]
        pub fn raw_index(&self) -> uint { self.idx as uint }
    }

    fn expect<T>(a: Option<T>, b: &str) -> T {
        match a {
            Some(a) => a,
            None => fail!("{}", b),
        }
    }

    // pub struct CachedEmpty {
    //     pos: uint,
    //     index: EmptyIndex
    // }

    // pub struct CachedFull {
    //     pos: uint,
    //     index: EmptyIndex
    // }

    // impl CachedIndex<EmptyIndex> {
    //     fn 
    // }

    #[inline]
    unsafe fn dealloc<T>(ptr: *mut T, len: uint) {
        if mem::size_of::<T>() != 0 {
            deallocate(ptr as *mut u8,
                       len * mem::size_of::<T>(),
                       mem::min_align_of::<T>())
        }
        // println!("ptr {}", ptr);
    }

    struct MutSafeIdx<'a, K, V> {
        pub h: &'a mut u64,
        k: &'a mut K,
        v: &'a mut V,
    }

    /// Represents the state of a bucket: it can either have a key/value
    /// pair (be full) or not (be empty). You cannot `take` empty buckets,
    /// and you cannot `put` into full buckets.
    pub enum BucketState {
        Empty(EmptyIndex),
        Full(FullIndex),
    }

    /// A hash that is not zero, since we use a hash of zero to represent empty
    /// buckets.
    #[deriving(PartialEq)]
    pub struct SafeHash {
        pub hash: u64,
    }

    impl<'a, K, V> MutSafeIdx<'a, K, V> {
        pub fn put(&mut self, hash: SafeHash, key: K, val: V) {
            debug_assert_eq!(*self.h, EMPTY_BUCKET);
            *self.h = hash.inspect();
            unsafe {
                overwrite(self.k, key);
                overwrite(self.v, val);
            }
        }
    }

    impl SafeHash {
        /// Peek at the hash value, which is guaranteed to be non-zero.
        #[inline(always)]
        pub fn inspect(&self) -> u64 { self.hash }
    }

    /// We need to remove hashes of 0. That's reserved for empty buckets.
    /// This function wraps up `hash_keyed` to be the only way outside this
    /// module to generate a SafeHash.
    pub fn make_hash<T: Hash<S>, S, H: Hasher<S>>(hasher: &H, t: &T) -> SafeHash {
        match hasher.hash(t) {
            // This constant is exceedingly likely to hash to the same
            // bucket, but it won't be counted as empty!
            EMPTY_BUCKET => SafeHash { hash: 0x8000_0000_0000_0000 },
            h            => SafeHash { hash: h },
        }
    }

    pub fn round_up_to_next(unrounded: uint, target_alignment: uint) -> uint {
        assert!(is_power_of_two(target_alignment));
        (unrounded + target_alignment - 1) & !(target_alignment - 1)
    }

    #[test]
    fn test_rounding() {
        assert_eq!(round_up_to_next(0, 4), 0);
        assert_eq!(round_up_to_next(1, 4), 4);
        assert_eq!(round_up_to_next(2, 4), 4);
        assert_eq!(round_up_to_next(3, 4), 4);
        assert_eq!(round_up_to_next(4, 4), 4);
        assert_eq!(round_up_to_next(5, 4), 8);
    }

    // Returns a tuple of (minimum required malloc alignment, hash_offset,
    // key_offset, val_offset, array_size), from the start of a mallocated array.
    fn calculate_offsets(
        hash_size: uint, hash_align: uint,
        keys_size: uint, keys_align: uint,
        vals_size: uint, vals_align: uint) -> (uint, uint, uint, uint, uint) {

        let hash_offset   = 0;
        let end_of_hashes = hash_offset + hash_size;

        let keys_offset   = round_up_to_next(end_of_hashes, keys_align);
        let end_of_keys   = keys_offset + keys_size;

        let vals_offset   = round_up_to_next(end_of_keys, vals_align);
        let end_of_vals   = vals_offset + vals_size;

        let min_align = cmp::max(hash_align, cmp::max(keys_align, vals_align));

        (min_align, hash_offset, keys_offset, vals_offset, end_of_vals)
    }

    #[test]
    fn test_offset_calculation() {
        assert_eq!(calculate_offsets(128, 8, 15, 1, 4, 4 ), (8, 0, 128, 144, 148));
        assert_eq!(calculate_offsets(3,   1, 2,  1, 1, 1 ), (1, 0, 3,   5,   6));
        assert_eq!(calculate_offsets(6,   2, 12, 4, 24, 8), (8, 0, 8,   24,  48));
    }

    impl<K, V> RawTable<K, V> {

        /// Does not initialize the buckets. The caller should ensure they,
        /// at the very least, set every hash to EMPTY_BUCKET.
        unsafe fn new_uninitialized(vec_capacity: uint) -> RawTable<K, V> {
            // let mut v = Vec::with_capacity(vec_capacity);
            if vec_capacity == 0 {
                RawTable { len: 0, cap: 0, ptr: 0 as *mut TriAry<K, V> }
            } else {
                let size = expect(vec_capacity.checked_mul(&mem::size_of::<TriAry<K, V>>()),
                                    "capacity overflow");
                let ptr = unsafe {
                    allocate(size, mem::min_align_of::<TriAry<K, V>>()) // min align 64 or next power of?
                };
                RawTable { len: 0, cap: vec_capacity, ptr: ptr as *mut TriAry<K, V> }
            }
            // // println!("{:?}", v.as_ptr());
            // unsafe {
            //     v.set_len(vec_capacity);
            //     // Vec::from_raw_parts(vec_capacity, vec_capacity, round_up_to_next(v.as_ptr() as uint, 64) as *mut RawChk<K, V>)
            //     // Vec::from_raw_parts(vec_capacity, vec_capacity, v.as_mut_ptr())
            // }
        }

        /// Creates a new raw table from a given capacity. All buckets are
        /// initially empty.
        #[allow(experimental)]
        pub fn new(capacity: uint) -> RawTable<K, V> {
            let vec_cap = capacity >> LOG2_CHUNK;
            unsafe {
                let mut table = RawTable::new_uninitialized(vec_cap);
                set_memory(table.ptr, 0u8, vec_cap);
                // for &(ref mut hashes, _, _) in ret.chunks.mut_iter() {
                //     set_memory(hashes.unsafe_mut_ref(0), 0u8, CHUNK);
                // }
                table
            }
        }

        // fn tuple_get idx & 7

        /// Reads a bucket at a given index, returning an enum indicating whether
        /// there's anything there or not. You need to match on this enum to get
        /// the appropriate types to pass on to most of the other functions in
        /// this module.
        pub fn peek(&self, index: uint) -> BucketState {
            // let hashes = unsafe { (*self.chunks.as_ptr().offset((idx as uint >> 3) as int)).ref0() };
            // TODO match all idxs with match?
            // let hash = unsafe { *(hashes.ref0() as *const u64).offset(idx & 7) };
            let (hash, _, _) = unsafe { self.ref_idx(index as int) };
            self.internal_peek(index, *hash)
        }
        pub fn internal_peek(&self, index: uint, hash: u64) -> BucketState {
            debug_assert!(index < self.capacity());

            let idx  = index as int;
            // let hashes = unsafe { (*self.chunks.as_ptr().offset((idx as uint >> 3) as int)).ref0() };
            // TODO match all idxs with match?
            // let hash = unsafe { *(hashes.ref0() as *const u64).offset(idx & 7) };

            let nocopy = marker::NoCopy;

            match hash { // or hash { &full_hash =>
                EMPTY_BUCKET =>
                    Empty(EmptyIndex {
                        idx:    idx,
                        nocopy: nocopy
                    }),
                full_hash =>
                    Full(FullIndex {
                        idx:    idx,
                        hash:   SafeHash { hash: full_hash },
                        nocopy: nocopy,
                    })
            }
        }

        fn ref_idx<'a>(&'a self, idx: int) -> (&'a u64, &'a K, &'a V) {
            #![inline(always)]
            let idx = idx as uint;
            unsafe {
                let &(ref hashes, ref keys, ref vals) = &*self.ptr.offset((idx >> LOG2_CHUNK) as int);
                (&'a hashes[idx & CHUNK_MASK], // CHUNK_MASK
                 &'a keys[idx & CHUNK_MASK],
                 &'a vals[idx & CHUNK_MASK])
            }
        }

        fn ptr_idx<'a>(&'a self, idx: int) -> (*const u64, *const K, *const V) {
            #![inline(always)]
            let idx = idx as uint;
            unsafe {
                let &(ref hashes, ref keys, ref vals) = &*self.ptr.offset((idx >> LOG2_CHUNK) as int);
                (&'a hashes[idx & CHUNK_MASK] as *const u64,
                 &'a keys[idx & CHUNK_MASK] as *const K,
                 &'a vals[idx & CHUNK_MASK] as *const V)
            }
        }

        pub fn ptr_mut_idx<'a>(&'a mut self, idx: int) -> (*mut u64, *mut K, *mut V) {
            #![inline(always)]
            let idx = idx as uint;
            unsafe {
                let &(ref mut hashes, ref mut keys, ref mut vals) = &mut *self.ptr.offset((idx >> LOG2_CHUNK) as int);
                (&'a mut hashes[idx & CHUNK_MASK] as *mut u64,
                 &'a mut keys[idx & CHUNK_MASK] as *mut K,
                 &'a mut vals[idx & CHUNK_MASK] as *mut V)
            }
        }

        // pub fn ptr_mut_idx<'a>(&'a mut self, idx: int) -> (*mut u64, *mut K, *mut V) {
        //     #![inline(always)]
        //     unsafe {
        //         // let &(ref mut hashes, ref mut keys, ref mut vals) = &mut *self.chunks.as_mut_ptr().offset((idx as uint >> 3) as int);
        //         // ((hashes.mut0() as *mut u64).offset(idx & 7),
        //         //  (keys.mut0()   as *mut  K ).offset(idx & 7),
        //         //  (vals.mut0()   as *mut  V ).offset(idx & 7))
        //         let idx = idx as uint;
        //         let base = self.chunks.as_mut_ptr() as *mut u8;
        //         let chk: uint = size_of::<TriAry<K, V>>() >> LOG2_CHUNK;
        //         let k = size_of::<K>() as int;
        //         let v = size_of::<V>() as int;
        //         // let koff = base.offset((chk * idx) as int + (idx & 7) as int * (k - chk as int) + 64)
        //         let hr = base.offset((chk * idx) as int + (idx & CHUNK_MASK) as int * (CHUNK as int - chk as int));
        //         let kr = base.offset((chk * idx) as int + (idx & CHUNK_MASK) as int * (k - chk as int) + 64);
        //         let vr = base.offset((chk * idx) as int + (idx & CHUNK_MASK) as int * (v - chk as int) + 64 + (k << LOG2_CHUNK));
        //         (hr as *mut u64, kr as *mut K, vr as *mut V)
        //     }
        // }

        /// Gets references to the key and value at a given index.
        pub fn read<'a>(&'a self, index: &FullIndex) -> (&'a K, &'a V) {
            let idx = index.idx as uint;

            unsafe {
                let &(ref hashes, ref keys, ref vals) = &*self.ptr.offset((idx >> LOG2_CHUNK) as int);
                debug_assert!(hashes[idx & CHUNK_MASK] != EMPTY_BUCKET);
                // (&'a *(keys.ref0() as *const K).offset(idx & 7),
                 // &'a *(vals.ref0() as *const V).offset(idx & 7))
                (&'a keys[idx & CHUNK_MASK],
                 &'a vals[idx & CHUNK_MASK])

            }
        }

        /// Gets references to the key and value at a given index, with the
        /// value's reference being mutable.
        pub fn read_mut<'a>(&'a mut self, index: &FullIndex) -> (&'a K, &'a mut V) {
            let idx = index.idx as uint;

            unsafe {
            let &(ref hashes, ref mut keys, ref mut vals) = &mut *self.ptr.offset((idx >> LOG2_CHUNK) as int);
                debug_assert!(hashes[idx & CHUNK_MASK] != EMPTY_BUCKET);
                // (&'a     *(keys.mut0() as *mut K).offset(idx & 7),
                 // &'a mut *(vals.mut0() as *mut V).offset(idx & 7))
                (&'a keys[idx & CHUNK_MASK],
                 &'a mut vals[idx & CHUNK_MASK])
            }
        }

        unsafe fn get_chunk(&mut self, idx: uint) -> &mut TriAry<K, V> {
            &mut *self.ptr.offset((idx >> LOG2_CHUNK) as int)
        }

        /// Read everything, mutably.
        pub fn safe_all_mut<'a>(&'a mut self, idx: int, empty: bool) -> MutSafeIdx<'a, K, V> {
            // makes insert and new_insert_drop slow!
            let idx = idx as uint;
            let &(ref mut hshs, ref mut keys, ref mut vals) = unsafe { self.get_chunk(idx) };

            if empty {
                // put into empty
                debug_assert_eq!(hshs[idx & CHUNK_MASK], EMPTY_BUCKET);
            }
            MutSafeIdx { 
                h: &'a mut hshs[idx & CHUNK_MASK],
                k: &'a mut keys[idx & CHUNK_MASK],
                v: &'a mut vals[idx & CHUNK_MASK]
            }
        }

        /// Puts a key and value pair, along with the key's hash, into a given
        /// index in the hashtable. Note how the `EmptyIndex` is 'moved' into this
        /// function, because that slot will no longer be empty when we return!
        /// A FullIndex is returned for later use, pointing to the newly-filled
        /// slot in the hashtable.
        ///
        /// Use `make_hash` to construct a `SafeHash` to pass to this function.
        pub fn put(&mut self, index: EmptyIndex, hash: SafeHash, k: K, v: V) -> FullIndex {
            let idx = index.idx;

            unsafe {
                let mut i = self.safe_all_mut(index.idx, true);
                i.put(hash, k, v);
            }

            unsafe {
                self.len += 1;
            }

            FullIndex { idx: idx, hash: hash, nocopy: marker::NoCopy }
        }

        /// Removes a key and value from the hashtable.
        ///
        /// This works similarly to `put`, building an `EmptyIndex` out of the
        /// taken FullIndex.
        pub fn take(&mut self, index: FullIndex) -> (EmptyIndex, K, V) {
            let idx  = index.idx;

            let (_, key, val) = self.ptr_idx(idx);
            let (hash, _, _) = self.ptr_mut_idx(idx);

            let tup = unsafe {
                // let &(ref mut hashes, ref keys, ref vals) = &mut *self.chunks.as_mut_ptr().offset((idx as uint >> 3) as int);
                debug_assert!(*hash != EMPTY_BUCKET);

                *hash = EMPTY_BUCKET;

                // Drop the mutable constraint.
                // let keys = (self.hashes as *mut u8).offset(self.keys() as int) as *mut K;
                // let vals = (self.hashes as *mut u8).offset(self.vals() as int) as *mut V;
                // let keys = keys as *const K;
                // let vals = vals as *const V;

                let k = ptr::read(key);
                let v = ptr::read(val);
                (EmptyIndex { idx: idx, nocopy: marker::NoCopy }, k, v)
            };


            self.len -= 1;
            // println!("take. {}", self.len);

            tup
        }

        // pub fn internal_take(&mut self, index: FullIndex) -> (EmptyIndex, K, V) {
        //     let idx  = index.idx;

        //     let (_, key, val) = self.ptr_idx(idx);
        //     let (hash, _, _) = self.ptr_mut_idx(idx);

        //     let tup = unsafe {
        //         // let &(ref mut hashes, ref keys, ref vals) = &mut *self.chunks.as_mut_ptr().offset((idx as uint >> 3) as int);
        //         debug_assert!(*hash != EMPTY_BUCKET);

        //         *hash = EMPTY_BUCKET;

        //         // Drop the mutable constraint.
        //         let k = ptr::read(key);
        //         let v = ptr::read(val);
        //         (EmptyIndex { idx: idx, nocopy: marker::NoCopy }, k, v)
        //     };

        //     unsafe {
        //         let len = self.size() - 1;
        //         self.chunks.set_len(len);
        //     }

        //     tup
        // }
        #[inline]
        pub fn try_grow(&mut self, new_cap: uint) -> bool {
            // println!("try_grow {} => {}", self.cap, new_cap)
            let has_reallocated = unsafe {
                if self.cap == 0 {
                    let size = new_cap * mem::size_of::<TriAry<K, V>>();
                    self.ptr = allocate(size, mem::min_align_of::<TriAry<K, V>>()) as *mut TriAry<K, V>;
                    true
                } else {
                    reallocate_inplace(self.ptr as *mut u8,
                                       new_cap * mem::size_of::<TriAry<K, V>>(),
                                       mem::min_align_of::<TriAry<K, V>>(),
                                       self.cap)
                }
            };
            if has_reallocated {
                self.cap = new_cap;
            }
            has_reallocated
        }

        pub fn as_mut_ptr(&self) -> *mut TriAry<K, V> {
            self.ptr
        }

        pub fn as_ptr(&self) -> *const TriAry<K, V> {
            self.ptr as *const TriAry<K, V>
        }

        #[inline]
        pub fn as_slice<'a>(&'a self) -> &'a [TriAry<K, V>] {
            unsafe {
                mem::transmute(Slice { data: self.as_mut_ptr() as *const TriAry<K, V>, len: self.cap })
            }
        }

        #[inline]
        pub fn as_mut_slice<'a>(&'a mut self) -> &'a mut [TriAry<K, V>] {
            unsafe {
                mem::transmute(Slice { data: self.as_mut_ptr() as *const TriAry<K, V>, len: self.cap })
            }
        }

        /// The hashtable's capacity, similar to a vector's.
        pub fn capacity(&self) -> uint {
            #![inline]
            self.cap << LOG2_CHUNK
        }

        /// The number of elements ever `put` in the hashtable, minus the number
        /// of elements ever `take`n.
        pub fn size(&self) -> uint {
            self.len
        }

        pub fn iter<'a>(&'a self) -> Entries<'a, K, V> {
            Entries { table: self, idx: 0, elems_seen: 0 }
        }

        pub fn mut_iter<'a>(&'a mut self) -> MutEntries<'a, K, V> {
            MutEntries { table: self, idx: 0, elems_seen: 0 }
        }

        pub fn move_iter(mut self) -> MoveEntries<K, V> {
            MoveEntries { table: self, idx: 0 }
            // let mut items = unsafe { transmute(TriAryIter::new(self.as_mut_slice())) };
            // MoveEntries {
            //     table: self,
            //     elems_seen: 0,
            //     items: items,
            //     triples: items.next().unwrap()
            // }
        }

        #[inline]
        pub fn get_mut<'a>(&'a mut self, index: uint) -> &'a mut TriAry<K, V> {
            &mut self.as_mut_slice()[index]
        }

        pub fn iter_from<'a>(&'a self, from: uint, to_skip: uint) -> TriVecEntries<K, V> {
            let elem_ptr = unsafe { self.ptr.offset(from as int) as *const TriAry<K, V> };
            let &(ref hsh, ref key, ref val) = unsafe { &*elem_ptr };
            let ptr = hsh as *const u64;
            let valptr = val as *const V;
            let off = to_skip as int;
            TriVecEntries {
                ptr: unsafe { ptr.offset(off) },
                keys: unsafe { (key as *const K).offset(off) },
                vals: unsafe { valptr.offset(off) },
                end: unsafe { (elem_ptr.offset(1)).offset(1) } as *const V, //align issue?
                marker: marker::ContravariantLifetime,
                // marker2: marker::NoCopy,
            }
        }

        pub fn shrink_to(&mut self, new_cap: uint) {
            if new_cap == 0 {
                if self.cap != 0 {
                    unsafe {
                        dealloc(self.ptr, self.cap)
                    }
                    self.cap = 0;
                }
            } else {
                let new_cap = new_cap >> LOG2_CHUNK;
                unsafe {
                    // Overflow check is unnecessary as the vector is already at
                    // least this large.
                    self.ptr = reallocate(self.ptr as *mut u8,
                                          new_cap * mem::size_of::<TriAry<K, V>>(),
                                          mem::min_align_of::<TriAry<K, V>>(),
                                          self.cap * mem::size_of::<TriAry<K, V>>()) as *mut TriAry<K, V>;
                }
                self.cap = new_cap;
            }
        }
    }

    pub fn mut_iter<'a, K, V>(this: &'a mut TriAry<K, V>) -> MutTriVecEntries<'a, K, V> {
        let &(ref mut hsh, ref mut key, ref mut val) = this;
        let ptr = hsh as *mut [u64, ..CHUNK] as *mut u64;
        let valptr = val as *mut [V, ..CHUNK] as *mut V;
        MutTriVecEntries {
            ptr: ptr,
            // end: unsafe { ptr.offset(CHUNK as int) },
            keys: key as *mut [K, ..CHUNK] as *mut K,
            vals: valptr,
            end: unsafe { (this as *mut TriAry<K, V>).offset(1) } as *mut V, //align issue?
            marker: marker::ContravariantLifetime,
            // marker2: marker::NoCopy,
        }
    }

    pub fn iter_at<'a, K, V>(this: &'a TriAry<K, V>, to_skip: int) -> TriVecEntries<'a, K, V> {
        let &(ref hsh, ref key, ref val) = this;
        let ptr = hsh as *const u64;
        let valptr = val as *const V;
        let off = to_skip as int;
        TriVecEntries {
            ptr: unsafe { ptr.offset(off) },
            keys: unsafe { (key as *const K).offset(off) },
            vals: unsafe { valptr.offset(off) },
            end: unsafe { (this as *const TriAry<K, V>).offset(1) } as *const V, //align issue?
            marker: marker::ContravariantLifetime,
            // marker2: marker::NoCopy,
        }
    }

    pub fn mut_iter_at<'a, K, V>(this: &'a mut TriAry<K, V>, to_skip: uint) -> MutTriVecEntries<'a, K, V> {
        let &(ref mut hsh, ref mut key, ref mut val) = this;
        let ptr = hsh as *mut [u64, ..CHUNK] as *mut u64;
        let valptr = val as *mut [V, ..CHUNK] as *mut V;
        let off = to_skip as int;
        MutTriVecEntries {
            ptr: unsafe { ptr.offset(off) },
            keys: unsafe { (key as *mut [K, ..CHUNK] as *mut K).offset(off) },
            vals: unsafe { valptr.offset(off) },
            end: unsafe { (this as *mut TriAry<K, V>).offset(1) } as *mut V, //align issue?
            marker: marker::ContravariantLifetime,
            // marker2: marker::NoCopy,
        }
    }

    pub struct TriVecEntries<'a, K, V> {
        ptr: *const u64,
        keys: *const K,
        vals: *const V,
        end: *const V,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> Iterator<(&'a u64, &'a K, &'a V)> for TriVecEntries<'a, K, V> {
        #[inline]
        fn next(&mut self) -> Option<(&'a u64, &'a K, &'a V)> {
            unsafe {
                if self.vals >= self.end {
                    None
                } else {
                    let tmp = (self.ptr, self.keys, self.vals);
                    self.ptr = self.ptr.offset(1);
                    self.keys = self.keys.offset(1);
                    self.vals = self.vals.offset(1);
                    Some(transmute(tmp))
                }
            }
        }
    }

    struct Bucket<'a, K, V> {
        pub hash: &'a mut u64,
        pub key:  &'a mut K,
        pub val:  &'a mut V
    }

    impl<'a, K, V> Bucket<'a, K, V> {
        fn put(&mut self, h: u64, k: K, v: V) {

        }
    }

    pub struct MutTriVecEntries<'a, K, V> {
        pub ptr: *mut u64,
        pub keys: *mut K,
        pub vals: *mut V,
        end: *mut V,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> Clone for MutTriVecEntries<'a, K, V> {
        fn clone(&self) -> MutTriVecEntries<'a, K, V> { *self }
    }

    impl<'a, K, V> Iterator<Bucket<'a, K, V>> for MutTriVecEntries<'a, K, V> {
        #[inline]
        fn next(&mut self) -> Option<Bucket<'a, K, V>> {
            unsafe {
                if self.vals >= self.end {
                    None
                } else {
                    let bucket = (self.ptr, self.keys, self.vals);
                    self.ptr = self.ptr.offset(1);
                    self.keys = self.keys.offset(1);
                    self.vals = self.vals.offset(1);
                    Some(transmute(bucket))
                }
            }
        }
    }

    pub struct TriAryIter<'a, K, V> {
        end: *mut TriAry<K, V>,
        ptr: *mut TriAry<K, V>,
        key: *mut TriAry<K, V>,
        val: *mut TriAry<K, V>,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> Clone for TriAryIter<'a, K, V> {
        fn clone(&self) -> TriAryIter<'a, K, V> { *self }
    }

    impl<'a, K, V> TriAryIter<'a, K, V> {
        pub fn new(slice: &'a mut [TriAry<K, V>]) -> TriAryIter<'a, K, V> {
            let len = slice.len();
            let ptr = slice.as_mut_ptr();
            unsafe {
                TriAryIter {
                    ptr: ptr,
                    end: ptr.offset(len as int),
                    key: (*ptr).mut1() as *mut [K, ..CHUNK] as *mut TriAry<K, V>,
                    val: (*ptr).mut2() as *mut [V, ..CHUNK] as *mut TriAry<K, V>,
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                }
            }
        }
    }

    impl<'a, K, V> Iterator<MutTriVecEntries<'a, K, V>> for TriAryIter<'a, K, V> {
        fn next(&mut self) -> Option<MutTriVecEntries<K, V>> {
            if self.ptr == self.end {
                None
            } else {
                unsafe {
                    // align issue?
                    let next_ptr = self.ptr.offset(1);
                    let r = MutTriVecEntries {
                        ptr: self.ptr as *mut u64,
                        keys: self.key as *mut K,
                        vals: self.val as *mut V,
                        end: next_ptr as *mut V,
                        // end: (self.ptr as *mut u64)
                        marker: marker::ContravariantLifetime,
                        // marker2: marker::NoCopy
                    };
                    self.ptr = next_ptr;
                    self.key = self.key.offset(1);
                    self.val = self.val.offset(1);
                    Some(r)
                }
            }
        }
    }

    pub struct TriArysCycle<'a, K, V> {
        end: *mut TriAry<K, V>,
        ptr: *mut TriAry<K, V>,
        key: *mut TriAry<K, V>,
        val: *mut TriAry<K, V>,
        cap: uint,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> Clone for TriArysCycle<'a, K, V> {
        fn clone(&self) -> TriArysCycle<'a, K, V> { *self }
    }

    impl<'a, K, V> TriArysCycle<'a, K, V> {
        pub fn new(slice: &'a mut [TriAry<K, V>], cap: uint) -> TriArysCycle<'a, K, V> {
            let len = slice.len();
            unsafe {
                let ptr = slice.as_mut_ptr();//.offset(off as int);
                TriArysCycle {
                    cap: cap,
                    ptr: ptr,
                    end: slice.as_mut_ptr().offset(len as int),
                    key: (*ptr).mut1() as *mut [K, ..CHUNK] as *mut TriAry<K, V>,
                    val: (*ptr).mut2() as *mut [V, ..CHUNK] as *mut TriAry<K, V>,
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                }
            }
        }
    // }

    // impl<'a, K, V> Iterator<MutTriVecEntries<'a, K, V>> for TriArysCycle<'a, K, V> {
        pub fn get(&mut self) -> MutTriVecEntries<K, V> {
            if self.ptr == self.end {
                let off = -(self.cap as int);
                unsafe {
                    self.ptr = self.ptr.offset(off);
                    self.key = self.key.offset(off);
                    self.val = self.val.offset(off);
                }
            }

            unsafe {
                // align issue?
                let next_ptr = self.ptr.offset(1);
                let ret = MutTriVecEntries {
                    ptr: self.ptr as *mut u64,
                    keys: self.key as *mut K,
                    vals: self.val as *mut V,
                    end: next_ptr as *mut V,
                    // end: (self.ptr as *mut u64)
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                };
                self.ptr = next_ptr;
                self.key = self.key.offset(1);
                self.val = self.val.offset(1);
                ret
            }
        }
    }

    pub struct TriArysWrap<'a, K, V> {
        end: *mut TriAry<K, V>,
        ptr: *mut TriAry<K, V>,
        key: *mut TriAry<K, V>,
        val: *mut TriAry<K, V>,
        cap: uint,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> TriArysWrap<'a, K, V> {
        pub fn new(slice: &'a mut [TriAry<K, V>], cap: uint) -> TriArysWrap<'a, K, V> {
            let len = slice.len();
            unsafe {
                let ptr = slice.as_mut_ptr();
                TriArysWrap {
                    cap: cap,
                    ptr: ptr,
                    end: slice.as_mut_ptr().offset(len as int),
                    key: (*ptr).mut1() as *mut [K, ..CHUNK] as *mut TriAry<K, V>,
                    val: (*ptr).mut2() as *mut [V, ..CHUNK] as *mut TriAry<K, V>,
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                }
            }
        }
    }

    impl<'a, K, V> Clone for TriArysWrap<'a, K, V> {
        fn clone(&self) -> TriArysWrap<'a, K, V> { *self }
    }

    impl<'a, K, V> Iterator<MutTriVecEntries<'a, K, V>> for TriArysWrap<'a, K, V> {
        fn next(&mut self) -> Option<MutTriVecEntries<K, V>> {
            if self.ptr == self.end {
                if self.cap == 0 {
                    return None;
                } else {
                    let off = -(self.cap as int);
                    unsafe {
                        self.ptr = self.ptr.offset(off);
                        self.key = self.key.offset(off);
                        self.val = self.val.offset(off);
                    }
                    self.cap = 0;
                }
            }

            unsafe {
                // align issue?
                let next_ptr = self.ptr.offset(1);
                let r = MutTriVecEntries {
                    ptr: self.ptr as *mut u64,
                    keys: self.key as *mut K,
                    vals: self.val as *mut V,
                    end: next_ptr as *mut V,
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                };
                self.ptr = next_ptr;
                self.key = self.key.offset(1);
                self.val = self.val.offset(1);
                Some(r)
            }
        }
    }

    pub struct ImmTriArysCycle<'a, K, V> {
        end: *const TriAry<K, V>,
        ptr: *const TriAry<K, V>,
        key: *const TriAry<K, V>,
        val: *const TriAry<K, V>,
        cap: uint,
        marker: marker::ContravariantLifetime<'a>,
        // marker2: marker::NoCopy
    }

    impl<'a, K, V> Clone for ImmTriArysCycle<'a, K, V> {
        fn clone(&self) -> ImmTriArysCycle<'a, K, V> { *self }
    }

    impl<'a, K, V> ImmTriArysCycle<'a, K, V> {
        pub fn new(slice: &'a [TriAry<K, V>], cap: uint) -> ImmTriArysCycle<'a, K, V> {
            let len = slice.len();
            unsafe {
                let ptr = slice.as_ptr();//.offset(off as int);
                ImmTriArysCycle {
                    cap: cap,
                    ptr: ptr,
                    end: slice.as_ptr().offset(len as int),
                    key: (*ptr).ref1() as *const [K, ..CHUNK] as *const TriAry<K, V>,
                    val: (*ptr).ref2() as *const [V, ..CHUNK] as *const TriAry<K, V>,
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                }
            }
        }
    // }

    // impl<'a, K, V> Iterator<MutTriVecEntries<'a, K, V>> for ImmTriArysCycle<'a, K, V> {
        pub fn get(&mut self) -> TriVecEntries<K, V> {
            if self.ptr == self.end {
                let off = -(self.cap as int);
                unsafe {
                    self.ptr = self.ptr.offset(off);
                    self.key = self.key.offset(off);
                    self.val = self.val.offset(off);
                }
            }

            unsafe {
                // align issue?
                let next_ptr = self.ptr.offset(1);
                let ret = TriVecEntries {
                    ptr: self.ptr as *const u64,
                    keys: self.key as *const K,
                    vals: self.val as *const V,
                    end: next_ptr as *const V,
                    // end: (self.ptr as *mut u64)
                    marker: marker::ContravariantLifetime,
                    // marker2: marker::NoCopy
                };
                self.ptr = next_ptr;
                self.key = self.key.offset(1);
                self.val = self.val.offset(1);
                ret
            }
        }
    }

    // `read_all_mut` casts a `*const u64` to a `*SafeHash`. Since we statically
    // ensure that a `FullIndex` points to an index with a non-zero hash,
    // and a `SafeHash` is just a `u64` with a different name, this is
    // safe.
    //
    // This test ensures that a `SafeHash` really IS the same size as a
    // `u64`. If you need to change the size of `SafeHash` (and
    // consequently made this test fail), `read_all_mut` needs to be
    // modified to no longer assume this.
    #[test]
    fn can_alias_safehash_as_u64() {
        assert_eq!(size_of::<SafeHash>(), size_of::<u64>())
    }

    /// Iterator over shared references to entries in a table.
    pub struct Entries<'a, K, V> {
        table: &'a RawTable<K, V>,
        idx: uint,
        elems_seen: uint,
    }

    /// Iterator over mutable references to entries in a table.
    pub struct MutEntries<'a, K, V> {
        table: &'a mut RawTable<K, V>,
        idx: uint,
        elems_seen: uint,
    }

    /// Iterator over the entries in a table, consuming the table.
    pub struct MoveEntries<K, V> {
        table: RawTable<K, V>,
        idx: uint,
        // items: TriAryIter<'static, K, V>,
        // triples: MutTriVecEntries<'static, K, V>
    }

    impl<'a, K, V> Iterator<(&'a K, &'a V)> for Entries<'a, K, V> {
        fn next(&mut self) -> Option<(&'a K, &'a V)> {
            while self.idx < self.table.capacity() {
                let i = self.idx;
                self.idx += 1;

                match self.table.peek(i) {
                    Empty(_)  => {},
                    Full(idx) => {
                        self.elems_seen += 1;
                        return Some(self.table.read(&idx));
                    }
                }
            }

            None
        }

        fn size_hint(&self) -> (uint, Option<uint>) {
            let size = self.table.size() - self.elems_seen;
            (size, Some(size))
        }
    }

    impl<'a, K, V> Iterator<(&'a K, &'a mut V)> for MutEntries<'a, K, V> {
        fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
            while self.idx < self.table.capacity() {
                let i = self.idx;
                self.idx += 1;

                match self.table.peek(i) {
                    Empty(_)  => {},
                    // the transmute here fixes:
                    // error: lifetime of `self` is too short to guarantee its contents
                    //        can be safely reborrowed
                    Full(idx) => unsafe {
                        self.elems_seen += 1;
                        return Some(transmute(self.table.read_mut(&idx)));
                    }
                }
            }

            None
        }

        fn size_hint(&self) -> (uint, Option<uint>) {
            let size = self.table.size() - self.elems_seen;
            (size, Some(size))
        }
    }

    impl<K, V> Iterator<(SafeHash, K, V)> for MoveEntries<K, V> {
        fn next(&mut self) -> Option<(SafeHash, K, V)> {
            while self.idx < self.table.capacity() {
                let i = self.idx;
                self.idx += 1;

                match self.table.peek(i) {
                    Empty(_) => {},
                    Full(idx) => {
                        let h = idx.hash();
                        let (_, k, v) = self.table.take(idx);
                        return Some((h, k, v));
                    }
                }
            }
            None
            //.mut_slice_to(vec_cap));
            // let unsfptr = unsafe{self as *mut HashMap<K, V, H>};
            // // (*unsfptr).table.set_len(new_capacity >> table::LOG2_CHUNK);
            // // let mut last_empty = false;

            // // let mut idx = 0;
            // for mut triples in items {
            //     // very important to keep this 
            //     // set_memory((triples.ptr as *mut table::TriAry<K, V>).offset(vec_cap as int) as *mut u8, 0u8, table::CHUNK);
                // for bucket in triples {

            // loop {
            //     let bucket = match self.triples.next() {
            //         Some(bucket) => bucket,
            //         None => {
            //             self.triples = match self.items.next() {
            //                 Some(t) => t,
            //                 None => return None
            //             };
            //             self.triples.next().unwrap()
            //         }
            //     };
            //     match bucket.hash {
            //         &0u64 => {} // empty or in place
            //         &full_hash => unsafe {
            //             let k = ptr::read(bucket.key as *mut K as *const K);
            //             let v = ptr::read(bucket.val as *mut V as *const V);

            //             let hash = *bucket.hash;
            //             *bucket.hash = 0u64;
            //             return Some((SafeHash{hash:hash}, k, v));
            //         }
            //     }
            // }
        }

        fn size_hint(&self) -> (uint, Option<uint>) {
            let size = self.table.size();
            (size, Some(size))
        }
    }

    impl<K: Clone, V: Clone> Clone for RawTable<K, V> {
        fn clone(&self) -> RawTable<K, V> {
            unsafe {
                let mut new_ht = RawTable::new_uninitialized(self.cap);

                for i in range(0, self.capacity()) {
                    match self.peek(i) {
                        Empty(_)  => {
                            let &(ref mut hashes, _, _) = new_ht.get_mut(i >> LOG2_CHUNK);
                            hashes[i & CHUNK_MASK] = EMPTY_BUCKET;
                        },
                        Full(idx) => {
                            let hash = idx.hash().inspect();
                            let (k, v) = self.read(&idx);

                            let &(ref mut hashes, ref mut keys, ref mut vals) = new_ht.get_mut(i >> LOG2_CHUNK);
                            hashes[i & CHUNK_MASK] = hash;
                // let keys = (new_ht.hashes as *mut u8).offset(new_ht.keys() as int) as *mut K;
                // let vals = (new_ht.hashes as *mut u8).offset(new_ht.vals() as int) as *mut V;
                            overwrite(&mut keys[i & CHUNK_MASK], (*k).clone());
                            overwrite(&mut vals[i & CHUNK_MASK], (*v).clone());
                        }
                    }
                }

                new_ht.len = self.len;

                new_ht
            }
        }
    }

    #[unsafe_destructor]
    impl<K, V> Drop for RawTable<K, V> {
        fn drop(&mut self) {
            // println!("start drop");
            // This is in reverse because we're likely to have partially taken
            // some elements out with `.move_iter()` from the front.
            for i in range_step_inclusive(self.capacity() as int - 1, 0, -1) {
                // Check if the size is 0, so we don't do a useless scan when
                // dropping empty tables such as on resize.
                if self.len == 0 { break }

                match self.peek(i as uint) {
                    Empty(_)  => {},
                    Full(idx) => { self.take(idx); }
                }
            }

            if self.cap != 0 {
                unsafe {
                    dealloc(self.ptr, self.cap)
                }
            }
        }
    }
}

static INITIAL_LOG2_CAP: uint = 5;//table::LOG2_CHUNK + 2;
static INITIAL_CAPACITY: uint = 1 << INITIAL_LOG2_CAP; // 2^5

/// The default behavior of HashMap implements a load factor of 90.9%.
/// This behavior is characterized by the following conditions:
///
/// - if `size * 1.1 < cap < size * 4` then shouldn't resize
/// - if `cap < minimum_capacity * 2` then shouldn't shrink
#[deriving(Clone)]
struct DefaultResizePolicy {
    /// Doubled minimal capacity. The capacity must never drop below
    /// the minimum capacity. (The check happens before the capacity
    /// is potentially halved.)
    minimum_capacity2: uint
}

impl DefaultResizePolicy {
    fn new(new_capacity: uint) -> DefaultResizePolicy {
        DefaultResizePolicy {
            minimum_capacity2: new_capacity << 1
        }
    }

    #[inline]
    fn capacity_range(&self, new_size: uint) -> (uint, uint) {
        ((new_size * 11) / 10, max(new_size << 3, self.minimum_capacity2))
    }

    #[inline]
    fn reserve(&mut self, new_capacity: uint) {
        self.minimum_capacity2 = new_capacity << 1;
    }
}

// The main performance trick in this hashmap is called Robin Hood Hashing.
// It gains its excellent performance from one key invariant:
//
//    If an insertion collides with an existing element, and that elements
//    "probe distance" (how far away the element is from its ideal location)
//    is higher than how far we've already probed, swap the elements.
//
// This massively lowers variance in probe distance, and allows us to get very
// high load factors with good performance. The 90% load factor I use is rather
// conservative.
//
// > Why a load factor of approximately 90%?
//
// In general, all the distances to initial buckets will converge on the mean.
// At a load factor of α, the odds of finding the target bucket after k
// probes is approximately 1-α^k. If we set this equal to 50% (since we converge
// on the mean) and set k=8 (64-byte cache line / 8-byte hash), α=0.92. I round
// this down to make the math easier on the CPU and avoid its FPU.
// Since on average we start the probing in the middle of a cache line, this
// strategy pulls in two cache lines of hashes on every lookup. I think that's
// pretty good, but if you want to trade off some space, it could go down to one
// cache line on average with an α of 0.84.
//
// > Wait, what? Where did you get 1-α^k from?
//
// On the first probe, your odds of a collision with an existing element is α.
// The odds of doing this twice in a row is approximately α^2. For three times,
// α^3, etc. Therefore, the odds of colliding k times is α^k. The odds of NOT
// colliding after k tries is 1-α^k.
//
// Future Improvements (FIXME!)
// ============================
//
// Allow the load factor to be changed dynamically and/or at initialization.
//
// Also, would it be possible for us to reuse storage when growing the
// underlying table? This is exactly the use case for 'realloc', and may
// be worth exploring.
//
// Future Optimizations (FIXME!)
// =============================
//
// The paper cited below mentions an implementation which keeps track of the
// distance-to-initial-bucket histogram. I'm suspicious of this approach because
// it requires maintaining an internal map. If this map were replaced with a
// hashmap, it would be faster, but now our data structure is self-referential
// and blows up. Also, this allows very good first guesses, but array accesses
// are no longer linear and in one direction, as we have now. There is also
// memory and cache pressure that this map would entail that would be very
// difficult to properly see in a microbenchmark.
//
// Another possible design choice that I made without any real reason is
// parameterizing the raw table over keys and values. Technically, all we need
// is the size and alignment of keys and values, and the code should be just as
// efficient (well, we might need one for power-of-two size and one for not...).
// This has the potential to reduce code bloat in rust executables, without
// really losing anything except 4 words (key size, key alignment, val size,
// val alignment) which can be passed in to every call of a `RawTable` function.
// This would definitely be an avenue worth exploring if people start complaining
// about the size of rust executables.
//
// There's also an "optimization" that has been omitted regarding how the
// hashtable allocates. The vector type has set the expectation that a hashtable
// which never has an element inserted should not allocate. I'm suspicious of
// implementing this for hashtables, because supporting it has no performance
// benefit over using an `Option<HashMap<K, V>>`, and is significantly more
// complicated.

/// A hash map implementation which uses linear probing with Robin
/// Hood bucket stealing.
///
/// The hashes are all keyed by the task-local random number generator
/// on creation by default, this means the ordering of the keys is
/// randomized, but makes the tables more resistant to
/// denial-of-service attacks (Hash DoS). This behaviour can be
/// overridden with one of the constructors.
///
/// It is required that the keys implement the `Eq` and `Hash` traits, although
/// this can frequently be achieved by using `#[deriving(Eq, Hash)]`.
///
/// Relevant papers/articles:
///
/// 1. Pedro Celis. ["Robin Hood Hashing"](https://cs.uwaterloo.ca/research/tr/1986/CS-86-14.pdf)
/// 2. Emmanuel Goossaert. ["Robin Hood
///    hashing"](http://codecapsule.com/2013/11/11/robin-hood-hashing/)
/// 3. Emmanuel Goossaert. ["Robin Hood hashing: backward shift
///    deletion"](http://codecapsule.com/2013/11/17/robin-hood-hashing-backward-shift-deletion/)
///
/// # Example
///
/// ```rust
/// use std::collections::HashMap;
///
/// // type inference lets us omit an explicit type signature (which
/// // would be `HashMap<&str, &str>` in this example).
/// let mut book_reviews = HashMap::new();
///
/// // review some books.
/// book_reviews.insert("Adventures of Huckleberry Finn",    "My favorite book.");
/// book_reviews.insert("Grimms' Fairy Tales",               "Masterpiece.");
/// book_reviews.insert("Pride and Prejudice",               "Very enjoyable.");
/// book_reviews.insert("The Adventures of Sherlock Holmes", "Eye lyked it alot.");
///
/// // check for a specific one.
/// if !book_reviews.contains_key(&("Les Misérables")) {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              book_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove(&("The Adventures of Sherlock Holmes"));
///
/// // look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for book in to_find.iter() {
///     match book_reviews.find(book) {
///         Some(review) => println!("{}: {}", *book, *review),
///         None => println!("{} is unreviewed.", *book)
///     }
/// }
///
/// // iterate over everything.
/// for (book, review) in book_reviews.iter() {
///     println!("{}: \"{}\"", *book, *review);
/// }
/// ```
#[deriving(Clone)]
pub struct HashMap<K, V, H = sip::SipHasher, R = DefaultResizePolicy> {
    // All hashes are keyed on these values, to prevent hash collision attacks.
    hasher: H,

    table: table::RawTable<K, V>,

    // We keep this at the end since it might as well have tail padding.
    resize_policy: DefaultResizePolicy,
}

#[inline]
pub fn bucket_dib(raw_index: uint, hash: u64, cap: uint) -> uint {
    // where the hash of the element that happens to reside at
    // `index_of_elem` tried to place itself first.
    // let first_probe_index = self.probe(&index_of_elem.hash(), 0);
    let hash_mask = cap - 1;

    // // So I heard a rumor that unsigned overflow is safe in rust..
    // let first_probe_index = (hash as uint) & hash_mask;
    // // if hash as uint & cap == cap {
    // //     return 0;
    // // }

    // // let raw_index = index_of_elem.raw_index();

    // if first_probe_index <= raw_index {
    //      // probe just went forward
    //     raw_index - first_probe_index
    // } else {
    //     // probe wrapped around the hashtable
    //     raw_index + (cap - first_probe_index)
    // }
    ((raw_index | cap) - (hash as uint & hash_mask)) & hash_mask
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> HashMap<K, V, H> {
    // Probe the `idx`th bucket for a given hash, returning the index of the
    // target bucket.
    //
    // This exploits the power-of-two size of the hashtable. As long as this
    // is always true, we can use a bitmask of cap-1 to do modular arithmetic.
    //
    // Prefer using this with increasing values of `idx` rather than repeatedly
    // calling `probe_next`. This reduces data-dependencies between loops, which
    // can help the optimizer, and certainly won't hurt it. `probe_next` is
    // simply for convenience, and is no more efficient than `probe`.
    fn probe(&self, hash: &table::SafeHash, idx: uint) -> uint {
        let hash_mask = self.table.capacity() - 1;

        // So I heard a rumor that unsigned overflow is safe in rust..
        ((hash.inspect() as uint) + idx) & hash_mask
    }

    // Generate the next probe in a sequence. Prefer using 'probe' by itself,
    // but this can sometimes be useful.
    fn probe_next(&self, probe: uint) -> uint {
        let hash_mask = self.table.capacity() - 1;
        (probe + 1) & hash_mask
    }

    fn make_hash<X: Hash<S>>(&self, x: &X) -> table::SafeHash {
        table::make_hash(&self.hasher, x)
    }

    /// Get the distance of the bucket at the given index that it lies
    /// from its 'ideal' location.
    ///
    /// In the cited blog posts above, this is called the "distance to
    /// initial bucket", or DIB.
    fn bucket_distance(&self, index_of_elem: &table::FullIndex) -> uint {
        // where the hash of the element that happens to reside at
        // `index_of_elem` tried to place itself first.
        // let first_probe_index = self.probe(&index_of_elem.hash(), 0);

        // let raw_index = index_of_elem.raw_index();

        // if first_probe_index <= raw_index {
        //      // probe just went forward
        //     raw_index - first_probe_index
        // } else {
        //     // probe wrapped around the hashtable
        //     raw_index + (self.table.capacity() - first_probe_index)
        // }
        bucket_dib(index_of_elem.raw_index(), index_of_elem.hash().inspect(), self.table.capacity())
    }

    /// Search for a pre-hashed key.
    fn search_hashed_generic(&self, hash: &table::SafeHash, is_match: |&K| -> bool)
        -> Option<table::FullIndex> {
        let unsfptr = self as *const HashMap<K, V, H>;
        let size = self.table.size();
        let cap = self.table.capacity();
        if cap == 0 {
            // TODO
            return None;
        }

        let full_skipped = (hash.inspect() as uint) & (cap - 1);
        let to_skip = full_skipped & table::CHUNK_MASK;
        let num_skipped = full_skipped >> table::LOG2_CHUNK;

        let mut it = unsafe {
            // table::iter_at((*unsfptr).table.chunks.as_slice().unsafe_ref(num_skipped), to_skip)
            self.table.iter_from(num_skipped, to_skip)
        };
        let limit = (num_skipped + 1) << table::LOG2_CHUNK;
        // let limit = (full_skipped & !table::CHUNK_MASK) + table::CHUNK;
        let mut idxs = range(full_skipped, limit);
        for (idx, (hsh, key, val)) in idxs.zip(it) {
            match hsh {
                &0u64 => {
                    return None; // hit an empty bucket
                }
                &full_hash => {
                    // We can finish the search early if we hit any bucket
                    // opt? shorter find_nonexisting, longer find_existing
                    // if bucket_dib(idx, full_hash, cap) < idx - full_skipped {
                    //     return None;
                    // }
                    if full_hash != hash.inspect() {
                        continue
                    }

                    if is_match(key) {
                        return Some(table::FullIndex{idx:idx as int,hash: table::SafeHash{hash:full_hash},nocopy: marker::NoCopy,});
                    }
                }
            }
        }

        let mut items = table::ImmTriArysCycle::new(self.table.as_slice().slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);
        let mut triples = items.get();

        let dib_idx = limit-(table::CHUNK - to_skip);
        for dib in range_inclusive(table::CHUNK - to_skip, size) {
            let (hsh, key, val) = match triples.next() {
                Some(t) => t,
                None => {
                    triples = items.get();
                    triples.next().unwrap()
                }
            };

            match hsh {
                &0u64 => {
                    return None; // hit an empty bucket
                }
                &full_hash => {
                    // We can finish the search early if we hit any bucket
                    if bucket_dib(dib + dib_idx, full_hash, cap) < dib {
                        return None;
                    }
                    if full_hash != hash.inspect() {
                        continue
                    }

                    if is_match(key) {
                        return Some(table::FullIndex{idx:((dib + dib_idx)&(cap - 1)) as int,hash: table::SafeHash{hash:full_hash},nocopy: marker::NoCopy,});
                    }
                }
            }
        }
        return None;
    }

    fn search_hashed(&self, hash: &table::SafeHash, k: &K) -> Option<table::FullIndex> {
        self.search_hashed_generic(hash, |k_| *k == *k_)
    }

    fn search_equiv<Q: Hash<S> + Equiv<K>>(&self, q: &Q) -> Option<table::FullIndex> {
        self.search_hashed_generic(&self.make_hash(q), |k| q.equiv(k))
    }

    /// Search for a key, yielding the index if it's found in the hashtable.
    /// If you already have the hash for the key lying around, use
    /// search_hashed.
    fn search(&self, k: &K) -> Option<table::FullIndex> {
        self.search_hashed(&self.make_hash(k), k)
    }

    fn pop_internal(&mut self, starting_index: table::FullIndex) -> Option<V> {
        let starting_probe = starting_index.raw_index();
        let size =  self.table.size();
        let cap = self.table.capacity();
        // let full_skipped = (starting_probe as uint) & (cap - 1);

        let ending_pos = {
            let full_skipped = (starting_probe + 1) & (cap - 1);
            let to_skip = full_skipped & table::CHUNK_MASK;
            let num_skipped = full_skipped >> table::LOG2_CHUNK;
            let mut items = table::TriArysCycle::new(self.table.as_mut_slice().mut_slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);
            let mut triples = unsafe {
                table::mut_iter_at((*(self as *mut HashMap<K, V, H>)).table.as_mut_slice().unsafe_mut_ref(num_skipped), to_skip)
            };
            // let mut idx = 0;

            // for bucket in triples {
            //     match bucket.hash {
            //         &0u64 /*if idx >= to_skip*/ => {
            //             *bucket.hash = hash.inspect();
            //             unsafe {
            //                 overwrite(bucket.key, k);
            //                 overwrite(bucket.val, v);
            //                 return;
            //             }
            //         }
            //         _ => {}
            //     }
            // }

            // for mut triples in items {
            //     for bucket in triples {
            //         match bucket.hash {
            //             &0u64 /*if idx >= to_skip*/ => {
            //                 *bucket.hash = hash.inspect();
            //                 unsafe {
            //                     overwrite(bucket.key, k);
            //                     overwrite(bucket.val, v);
            //                     return;
            //                 }
            //             }
            //             _ => {}
            //         }
            //         // idx += 1;
            //     }
            //     // triples = triples_n;
            // }
            // let mut probe = self.probe_next(starting_probe);
            let mut bucket = triples.next().unwrap();
            for idx in range(full_skipped, full_skipped + size) {
                match bucket.hash {
                    &0u64 => {}
                    &full_hash => {
                        if bucket_dib(idx, full_hash, cap) != 0 {
                            bucket = match triples.next() {
                                Some(bucket) => bucket,
                                None => {
                                    triples = items.get();
                                    triples.next().unwrap()
                                }
                            };
                            continue;
                        }
                    }
                }
                // match self.table.peek(probe) {
                //     table::Empty(_) => {}, // empty bucket. this is the end of our shifting.
                //     table::Full(idx) => {
                //         // Bucket that isn't us, which has a non-zero probe distance.
                //         // This isn't the ending index, so keep searching.
                //         if self.bucket_distance(&idx) != 0 {
                //             probe = self.probe_next(probe);
                //             continue;
                //         }

                //         // if we do have a bucket_distance of zero, we're at the end
                //         // of what we need to shift.
                //     }
                // }
                break;
            }

            bucket.hash as *mut u64
        };

        let to_skip = starting_probe & table::CHUNK_MASK;
        let num_skipped = starting_probe >> table::LOG2_CHUNK;

        let retval = {
            let mut items = table::TriArysCycle::new(self.table.as_mut_slice().mut_slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);
            let mut triples = unsafe {
                table::mut_iter_at((*(self as *mut HashMap<K, V, H>)).table.as_mut_slice().unsafe_mut_ref(num_skipped), to_skip)
            };
            // let (_, _, retval) = self.table.take(starting_index);

            // let mut      probe = starting_probe;
            // let mut next_probe = self.probe_next(probe);
            let mut bucket = triples.next().unwrap();
            let retval = unsafe {
                *bucket.hash = 0u64;
                ptr::read(bucket.key as *mut K as *const K);
                ptr::read(bucket.val as *mut V as *const V)
            };

            // backwards-shift all the elements after our newly-deleted one.
            // while next_probe != ending_probe {
            loop {
                let next_bucket = match triples.next() {
                    Some(bucket) => bucket,
                    None => {
                        triples = items.get();
                        triples.next().unwrap()
                    }
                };

                if next_bucket.hash as *mut u64 == ending_pos {
                    // println!("ok {}", ending_pos);
                    // no?
                    // bucket = next_bucket;
                    break;
                }
                // println!("{} != {}", next_bucket.hash as *mut u64, ending_pos);

                match next_bucket.hash {
                    &0u64 => {
                        *bucket.hash = 0u64;
                    }
                    _ => unsafe {
                        overwrite(bucket.key, ptr::read(next_bucket.key as *mut K as *const K));
                        overwrite(bucket.val, ptr::read(next_bucket.val as *mut V as *const V));
                        *bucket.hash = replace(next_bucket.hash, 0u64);
                    }
                }

                bucket = next_bucket;
                // match self.table.peek(next_probe) {
                //     table::Empty(_) => {
                //         // nothing to shift in. just empty it out.
                //         match self.table.peek(probe) {
                //             table::Empty(_) => {},
                //             table::Full(idx) => { self.table.take(idx); }
                //         }
                //     },
                //     table::Full(next_idx) => {
                //         // something to shift. move it over!
                //         let next_hash = next_idx.hash();
                //         let (_, next_key, next_val) = self.table.take(next_idx);
                //         match self.table.peek(probe) {
                //             table::Empty(idx) => {
                //                 self.table.put(idx, next_hash, next_key, next_val);
                //             },
                //             table::Full(idx) => {
                //                 let (emptyidx, _, _) = self.table.take(idx);
                //                 self.table.put(emptyidx, next_hash, next_key, next_val);
                //             }
                //         }
                //     }
                // }

                // probe = next_probe;
                // next_probe = self.probe_next(next_probe);
            }

            match bucket.hash {
                &0u64 => {}
                _ => {
                    *bucket.hash = 0u64;
                }
            }
            retval
        };
        // Done the backwards shift, but there's still an element left!
        // Empty it out.
        // match self.table.peek(probe) {
        //     table::Empty(_) => {},
        //     table::Full(idx) => { self.table.take(idx); }
        // }

        // Now we're done all our shifting. Return the value we grabbed
        // earlier.
        self.table.len -= 1;
        return Some(retval);
    }

    /// Like `pop`, but can operate on any type that is equivalent to a key.
    #[experimental]
    pub fn pop_equiv<Q:Hash<S> + Equiv<K>>(&mut self, k: &Q) -> Option<V> {
        if self.table.size() == 0 {
            return None
        }

        let potential_new_size = self.table.len - 1;
        self.make_some_room(potential_new_size);

        let starting_index = match self.search_equiv(k) {
            Some(idx) => idx,
            None      => return None,
        };

        self.pop_internal(starting_index)
    }

    fn insert_first_empty(&mut self, hash: table::SafeHash, k: K, v: V) {
        let size = self.table.size();
        let cap = self.table.capacity();

        let full_skipped = (hash.inspect() as uint) & (cap - 1);
        let to_skip = full_skipped & table::CHUNK_MASK;
        let num_skipped = full_skipped >> table::LOG2_CHUNK;

        let full_end = (full_skipped + size) & (cap - 1);

        // let mut items = table::TriArysCycle::new(self.table.as_mut_slice().mut_slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);

        // let mut triples = unsafe {
        //     let unsfptr = self as *mut HashMap<K, V, H>;
        //     table::mut_iter_at((*unsfptr).table.as_mut_slice().unsafe_mut_ref(num_skipped), to_skip)
        // };

        // for _ in range_inclusive(0u, size) {
        //     let bucket = match triples.next() {
        //         Some(bucket) => bucket,
        //         None => {
        //             triples = items.get();
        //             triples.next().unwrap()
        //         }
        //     };

        //     match bucket.hash {
        //         &0u64 => {
        //             *bucket.hash = hash.inspect();
        //             unsafe {
        //                 overwrite(bucket.key, k);
        //                 overwrite(bucket.val, v);
        //                 return;
        //             }
        //         }
        //         _ => {}
        //     }
        // }

        let mut items = table::TriArysWrap::new(self.table.as_mut_slice().mut_slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);
        let mut triples = unsafe {
            table::mut_iter_at((*(self as *mut HashMap<K, V, H>)).table.as_mut_slice().unsafe_mut_ref(num_skipped), to_skip)
        };
        // let mut idx = 0;

        for bucket in triples {
            match bucket.hash {
                &0u64 /*if idx >= to_skip*/ => {
                    *bucket.hash = hash.inspect();
                    unsafe {
                        overwrite(bucket.key, k);
                        overwrite(bucket.val, v);
                        return;
                    }
                }
                _ => {}
            }
        }

        for mut triples in items {
            for bucket in triples {
                match bucket.hash {
                    &0u64 /*if idx >= to_skip*/ => {
                        *bucket.hash = hash.inspect();
                        unsafe {
                            overwrite(bucket.key, k);
                            overwrite(bucket.val, v);
                            return;
                        }
                    }
                    _ => {}
                }
                // idx += 1;
            }
            // triples = triples_n;
        }
        // We really shouldn't be here.
        fail!("Internal HashMap error: Out of space.");
    }

    fn overwrite_hashed_existing_with(&mut self, hash: table::SafeHash, k: K, v: V,
    already_exists: |V, &mut V|) -> &mut V {
        let size = self.table.size();
        let cap = self.table.capacity();

        let full_skipped = (hash.inspect() as uint) & (cap - 1);
        let to_skip = full_skipped & table::CHUNK_MASK;
        let num_skipped = full_skipped >> table::LOG2_CHUNK;

        let mut items = table::TriArysCycle::new(self.table.as_mut_slice().mut_slice_from(num_skipped + 1), cap >> table::LOG2_CHUNK);

        let mut triples = unsafe {
            let unsfptr = self as *mut HashMap<K, V, H>;
            table::mut_iter_at((*unsfptr).table.as_mut_slice().unsafe_mut_ref(num_skipped), to_skip)
        };

        for (dib, idx) in range_inclusive(0u, size).zip(range_inclusive(full_skipped, full_skipped + size)) {
        // for dib in range_inclusive(0u, size) {
            // let idx = (dib + full_skipped) & (cap - 1);
            let bucket = match triples.next() {
                Some(bucket) => bucket,
                None => {
                    triples = items.get();
                    triples.next().unwrap()
                }
            };

            match bucket.hash {
                &0u64 => {
                    *bucket.hash = hash.inspect();
                    unsafe {
                        overwrite(bucket.key, k);
                        overwrite(bucket.val, v);
                        return bucket.val;
                    }
                }
                &full_hash => {
                    if full_hash == hash.inspect() {
                        if k == *bucket.key {
                            // slowdown?
                            already_exists(v, bucket.val);
                            return bucket.val;
                        }
                    }
                    // let probe_dib = probe_luck_diff(full_hash, full_skipped, cap);
                    let probe_dib = bucket_dib(dib + full_skipped, full_hash, cap);
                    if probe_dib < dib {
                    // if full_skipped < (full_hash as uint & (cap - 1)) {
                    // if (((full_skipped | cap) - ((full_skipped + dib) & (cap - 1))) & cap) + (full_hash as uint & (cap - 1)) > full_skipped {
                    // let skipped = full_skipped;
                    // if (((skipped|cap) - idx - 1) & ((idx|cap)-(full_hash as uint & (cap - 1))) & cap) + (full_hash as uint & (cap - 1)) > full_skipped {
                    //     println!("({} & {} & cap) + {} > {}. dib {} idx {}", ((skipped|cap) - idx - 1), ((idx|cap)-(full_hash as uint & (cap - 1))), (full_hash as uint & (cap - 1)), full_skipped, dib, idx);
                        // let bval: *mut V = val;
                        // ----- ROBIN HOOD
                        // do_robin_hood(hsh, key, val,
                        //     full_hash, k, v, idx, probe_dib,
                        //     &mut items, &mut triples, size, cap);
                        // let (mut hash_ref, mut key_ref, mut val_ref) = (bucket.hash, bucket.key, bucket.val);
                        let mut dib_param = probe_dib;//bucket_dib(idx, full_hash, cap);
                        // println!("{} < {}; cap {}", dib_param, dib, cap);
                        // assert!(dib_param < dib);
                        let mut robin_bucket = bucket;
                        let (mut hash, mut k, mut v) = (hash.inspect(), k, v);
                        let mut index = (dib + full_skipped) & (cap - 1);
                        let mut idx_dib = index - dib_param;
                        'outer: loop {
                            let (old_hash, old_key, old_val) = {
                                let old_hash = replace(robin_bucket.hash, hash);
                                let old_key  = replace(robin_bucket.key,  k);
                                let old_val  = replace(robin_bucket.val,  v);

                                (old_hash, old_key, old_val)
                            };

                            let mut items_clone = items.clone();
                            let mut triples_clone = triples.clone();

                            for dib in range(dib_param + 1, size) {
                                let bucket = match triples_clone.next() {
                                    Some(bucket) => bucket,
                                    None => {
                                        triples_clone = items_clone.get();
                                        triples_clone.next().unwrap()
                                    }
                                };

                                match bucket.hash {
                                    &0u64 => {
                                        // Finally. A hole!
                                        *bucket.hash = old_hash;
                                        unsafe {
                                            overwrite(bucket.key, old_key);
                                            overwrite(bucket.val, old_val);
                                        }
                                        return bucket.val;
                                    }
                                    &full_hash => {
                                        let probe_dib = bucket_dib(dib + idx_dib, full_hash, cap);
                                        if probe_dib < dib {
                                        // if (full_hash as uint & (cap - 1)) < (full_hash as uint & (cap - 1)) {
                                            robin_bucket = bucket;
                                            dib_param = probe_dib;//bucket_dib(idx, full_hash, cap);//probe_dib;
                                            idx_dib = ((dib + idx_dib) & (cap - 1)) - probe_dib;
                                            hash = old_hash;
                                            k = old_key;
                                            v = old_val;
                                            items = items_clone;
                                            triples = triples_clone;
                                            continue 'outer;
                                        }
                                    }
                                }
                            }

                            fail!("HashMap fatal error: 100% load factor?");
                        }

                        // unsafe {
                            // (*unsfptr).table.size = potential_new_size;
                        // }
                        // return (unsafe {&mut(*bval)}, None);
                        // ----- ROBIN HOOD
                    }
                    // else {
                    //     assert!(bucket_dib(idx, full_hash, cap) >= dib)
                    // }
                }
            }
        }
        // We really shouldn't be here.
        fail!("Internal HashMap error: Out of space.");
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> Collection for HashMap<K, V, H> {
    /// Return the number of elements in the map
    fn len(&self) -> uint { self.table.size() }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> Mutable for HashMap<K, V, H> {
    /// Clear the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    fn clear(&mut self) {
        // Prevent reallocations from happening from now on. Makes it possible
        // for the map to be reused but has a downside: reserves permanently.
        self.resize_policy.reserve(self.table.size());

        for i in range(0, self.table.capacity()) {
            match self.table.peek(i) {
                table::Empty(_)  => {},
                table::Full(idx) => { self.table.take(idx); }
            }
        }
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> Map<K, V> for HashMap<K, V, H> {
    fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
        self.search(k).map(|idx| {
            let (_, v) = self.table.read(&idx);
            v
        })
    }

    fn contains_key(&self, k: &K) -> bool {
        self.search(k).is_some()
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> MutableMap<K, V> for HashMap<K, V, H> {
    fn find_mut<'a>(&'a mut self, k: &K) -> Option<&'a mut V> {
        match self.search(k) {
            None => None,
            Some(idx) => {
                let (_, v) = self.table.read_mut(&idx);
                Some(v)
            }
        }
    }

    fn swap(&mut self, k: K, v: V) -> Option<V> {
        let mut potential_new_size = self.table.len + 1;
        let hash = self.make_hash(&k);
        self.make_some_room(potential_new_size);

        // println!("swap {:?}", self.table)
        let mut ret = None;
        self.overwrite_hashed_existing_with(hash, k, v, |val, val_ref| {
            ret = Some(replace(val_ref, val));
            potential_new_size -= 1;
        });
        self.table.len = potential_new_size;
        ret
    }

    fn pop(&mut self, k: &K) -> Option<V> {
        if self.table.size() == 0 {
            return None
        }

        let potential_new_size = self.table.size() - 1;
        self.make_some_room(potential_new_size);
        let starting_index = match self.search(k) {
            Some(idx) => idx,
            None      => return None,
        };

        self.pop_internal(starting_index)
    }
}

impl<K: Hash + Eq, V> HashMap<K, V, sip::SipHasher> {
    /// Create an empty HashMap.
    pub fn new() -> HashMap<K, V, sip::SipHasher> {
        // HashMap::with_capacity(INITIAL_CAPACITY)
        let mut r = rand::task_rng();
        let r0 = r.gen();
        let r1 = r.gen();
        let hasher = sip::SipHasher::new_with_keys(r0, r1);
        // HashMap::with_capacity_and_hasher(INITIAL_CAPACITY, hasher)
        HashMap {
            hasher:        hasher,
            resize_policy: DefaultResizePolicy::new(INITIAL_CAPACITY),
            table:         table::RawTable::new(0),
        }
    }

    /// Creates an empty hash map with the given initial capacity.
    pub fn with_capacity(capacity: uint) -> HashMap<K, V, sip::SipHasher> {
        let mut r = rand::task_rng();
        let r0 = r.gen();
        let r1 = r.gen();
        let hasher = sip::SipHasher::new_with_keys(r0, r1);
        HashMap::with_capacity_and_hasher(capacity, hasher)
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> HashMap<K, V, H> {
    /// Creates an empty hashmap which will use the given hasher to hash keys.
    ///
    /// The creates map has the default initial capacity.
    pub fn with_hasher(hasher: H) -> HashMap<K, V, H> {
        HashMap {
            hasher:        hasher,
            resize_policy: DefaultResizePolicy::new(INITIAL_CAPACITY),
            table:         table::RawTable::new(0),
        }
    }

    /// Create an empty HashMap with space for at least `capacity`
    /// elements, using `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    pub fn with_capacity_and_hasher(capacity: uint, hasher: H) -> HashMap<K, V, H> {
        let cap = num::next_power_of_two(max(INITIAL_CAPACITY, capacity));
        HashMap {
            hasher:        hasher,
            resize_policy: DefaultResizePolicy::new(cap),
            table:         table::RawTable::new(cap),
        }
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> HashMap<K, V, H> {
    /// The hashtable will never try to shrink below this size. You can use
    /// this function to reduce reallocations if your hashtable frequently
    /// grows and shrinks by large amounts.
    ///
    /// This function has no effect on the operational semantics of the
    /// hashtable, only on performance.
    pub fn reserve(&mut self, new_minimum_capacity: uint) {
        let cap = num::next_power_of_two(
            max(INITIAL_CAPACITY, new_minimum_capacity));

        self.resize_policy.reserve(cap);

        if self.table.capacity() < cap {
            self.resize(cap);
        }
    }

    /// Resizes the internal vectors to a new capacity. It's your responsibility to:
    ///   1) Make sure the new capacity is enough for all the elements, accounting
    ///      for the load factor.
    ///   2) Ensure new_capacity is a power of two.
    fn resize(&mut self, new_capacity: uint) {
        assert!(self.table.size() <= new_capacity);
        assert!(num::is_power_of_two(new_capacity));

        let old_table = replace(&mut self.table, table::RawTable::new(new_capacity));
        let old_size  = old_table.size();

        if old_table.ptr.is_not_null() {
            // let mut new_size = 0;
            for (h, k, v) in old_table.move_iter() {
                // self.overwrite_hashed_existing_with(h, k, v, |_, _| {});
                self.insert_first_empty(h, k, v);
                self.table.len += 1;
            }
        }

        // self.table.size = new_size;
        assert_eq!(self.table.size(), old_size);
    }

    //     let vec_cap = cap >> table::LOG2_CHUNK;
    //     let old_size = self.table.size();
    //     // println!("growing to {}", new_capacity >> table::LOG2_CHUNK);
    //     unsafe {
    //         ptr::set_memory(self.table.as_mut_ptr().offset(vec_cap as int), 0u8, cap >> table::LOG2_CHUNK);
    //     }

    //     // let keep_len = self.table.size;
    //     unsafe {
    //         let mut idx = 0;
    //         while idx < cap {
    //             let i = idx;
    //             idx += 1;

    //             match self.table.peek(i) {
    //                 table::Empty(_) => {},
    //                 table::Full(idx) => {
    //                     let h = idx.hash();
    //                     if h.inspect() as uint & cap == cap {
    //                         let (_, k, v) = self.table.take(idx);
    //                         self.overwrite_hashed_existing_with(h, k, v, |_, _| ());
    //                         self.table.len += 1;
    //                     }
    //                 }
    //             }
    //         }

    //         // let mut items = table::TriAryIter::new(self.table.as_mut_slice().mut_slice_to(vec_cap));
    //         // let unsfptr = unsafe{self as *mut HashMap<K, V, H>};
    //         // // (*unsfptr).table.set_len(new_capacity >> table::LOG2_CHUNK);
    //         // // let mut last_empty = false;

    //         // // let mut idx = 0;
    //         // for mut triples in items {
    //         //     // very important to keep this 
    //         //     // set_memory((triples.ptr as *mut table::TriAry<K, V>).offset(vec_cap as int) as *mut u8, 0u8, table::CHUNK);
    //         //     for bucket in triples {
    //         //         match (*bucket.hash) as uint & cap {
    //         //             0u => {} // empty or in place
    //         //             _ => {
    //         //                 // Put it where it would have been
    //         //                 let k = ptr::read(bucket.key as *mut K as *const K);
    //         //                 let v = ptr::read(bucket.val as *mut V as *const V);

    //         //                 let hash = *bucket.hash;
    //         //                 *bucket.hash = 0u64;
    //         //                 // let half_off = (cap >> table::LOG2_CHUNK) as int;
    //         //                 // let (hsh2, key2, val2) = (
    //         //                 //     (hsh as *mut u64 as *mut table::TriAry<K, V>).offset(half_off) as *mut u64,
    //         //                 //     (key as *mut K as *mut table::TriAry<K, V>).offset(half_off) as *mut K,
    //         //                 //     (val as *mut V as *mut table::TriAry<K, V>).offset(half_off) as *mut V,
    //         //                 // );
    //         //                 // if last_empty && *hsh2 == 0u64 {
    //         //                 //     unsafe {
    //         //                 //         *hsh2 = hash;
    //         //                 //         overwrite(key2, k);
    //         //                 //         overwrite(val2, v);
    //         //                 //         // (*unsfptr).table.size = potential_new_size;
    //         //                 //     }
    //         //                 // }
    //         //                 // else {
    //         //                 // (*unsfptr).pop_internal(table::FullIndex{idx:idx as int,hash: table::SafeHash{hash:hash},nocopy: marker::NoCopy,});
    //         //                 (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
    //         //                 // }
    //         //                 // last_empty = false;
    //         //             }
    //         //         }
    //         //         // idx += 1;
    //         //     }
    //         // }
    //     }
    //     assert_eq!(self.table.size(), old_size);
    // }

    fn resize_inplace(&mut self, cap: uint, new_capacity: uint) {
        use mem;
        let vec_cap = cap >> table::LOG2_CHUNK;
        // let cap_shift = cap.trailing_zeros();
        let old_size = self.table.size();
        // println!("growing to {}", new_capacity >> table::LOG2_CHUNK);
        unsafe {
            ptr::set_memory(self.table.as_mut_ptr().offset(vec_cap as int), 0u8, (new_capacity - cap) >> table::LOG2_CHUNK);
        }

        // let keep_len = self.table.size;
        unsafe {
            // let mut idx = 0;
            // while idx < cap {
            //     let i = idx;
            //     idx += 1;

            //     match self.table.peek(i) {
            //         table::Empty(_) => {},
            //         table::Full(idx) => {
            //             let h = idx.hash();
            //             if h.inspect() as uint & cap == cap {
            //                 let (_, k, v) = self.table.take(idx);
            //                 self.overwrite_hashed_existing_with(h, k, v, |_, _| ());
            //                 self.table.len += 1;
            //             }
            //         }
            //     }
            // }

            let mut items = table::TriAryIter::new(self.table.as_mut_slice().mut_slice_to(vec_cap));
            // let mut triples = items.next().unwrap();
            let unsfptr = unsafe{self as *mut HashMap<K, V, H>};
            // (*unsfptr).table.set_len(new_capacity >> table::LOG2_CHUNK);
            // let mut last_empty = false;
            let mut cap_tz = cap.trailing_zeros();
            let mut idx = 0u;
            // let mut swapping = false;
            // let mut swap_items = items.clone();
            // let mut swap_triples = mem::uninit();
            for mut triples in items {
                // let mut swapping = 1;
                // let mut not_first = false;
                for bucket in triples {
                    match bucket.hash {
                        &0u64 => { // empty or in place
                            // swapping = 0;
                            // not_first = true;
                        }
                        _ /*if full_hash as uint & (new_capacity - 1) != idx*/ => {
                            // if *bucket.hash as uint & (new_capacity - 1) == idx {
                            //     not_first = true;
                            //     idx += 1;
                            //     continue;
                            // }
                            let k = ptr::read(bucket.key as *mut K as *const K);
                            let v = ptr::read(bucket.val as *mut V as *const V);

                            let hash = replace(bucket.hash, 0u64);
                            // if swapping == 1 {
                            //     let off = -1;
                            //     *(bucket.hash as *mut u64).offset(off) = hash;
                            //     overwrite((bucket.key as *mut K).offset(off), k);
                            //     overwrite((bucket.val as *mut V).offset(off), v);
                            // }
                            // else {

                            // let branchless_half = ((full_hash as uint) >> cap_shift) & 1;
                            // match hash as uint & cap {
                            //     // idx => {}
                            //     0 => {
                                    (*unsfptr).insert_first_empty(table::SafeHash{hash:hash}, k, v);
                            //     }
                            //     _ => {
                            //         (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
                            //     }
                            // }
                            // if hash as uint & (new_capacity - 1) == idx {
                            // }
                            // else if hash as uint & cap != 0 {
                            //     // todo: branchless?
                            //     // if not_first {
                            //     // let vref = (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
                            //     // if vref as *mut V > bucket.val as *mut V {
                            //     // if swapping <= 0 {
                            //     //     swapping -= 1;
                            //     // }
                            //     // }
                            //     // else {
                            //         // swapping = (bucket.val as *mut V as uint - vref as *mut V as uint) / mem::size_of::<V>();
                            //     // }
                            //     // }
                            //     (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
                            // }
                            // else {
                            //     (*unsfptr).insert_first_empty(table::SafeHash{hash:hash}, k, v);
                            // }
                            // else if hash as uint & (new_capacity - 1) == idx {
                            //     swapping = 0;
                            //     idx += 1;
                            //     continue;
                            // }
                            // else if bucket_dib(idx, hash, new_capacity) < swapping {
                            //     // if swapping == 1 {
                            //     //     idx += 1;
                            //     //     continue;
                            //     // }
                            //     swapping = 0;
                            // }
                            //---
                            // else if swapping < 0 /*&& (full_hash as uint & (new_capacity - 1)) >= idx - swapping*/ {
                            //     // let off = -(swapping as int);
                            //     *(bucket.hash as *mut u64).offset(swapping) = hash;
                            //     overwrite((bucket.key as *mut K).offset(swapping), k);
                            //     overwrite((bucket.val as *mut V).offset(swapping), v);
                            //     idx += 1;
                            //     continue;
                            // }
                            //---
                            // else {
                                // (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
                            // }
                            // else {
                            //     not_first = true;
                            // }

                            // if hash as uint & cap == 0 {
                            //     swapping = 0;
                            // }
                            // else {
                            //     swapping = 1;
                            // }
                            // swapping = (hash as uint >> cap_tz) & 1;

                            // (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
                            // }
                        }
                        // }
                        // _ => { // empty or in place
                        // }
                    }
                    idx += 1;
                }
            }
            // loop {
            //     // let (prev_items, prev_triples) = (items.clone(), triples.clone());
            //     let bucket = match triples.next() {
            //         Some(bucket) => bucket,
            //         None => {
            //             triples = match items.next() {
            //                 Some(t) => t,
            //                 None => break
            //             };
            //             triples.next().unwrap()
            //         }
            //     };
            //     // very important to keep this 
            //     // set_memory((triples.ptr as *mut table::TriAry<K, V>).offset(vec_cap as int) as *mut u8, 0u8, table::CHUNK);
            //     // for bucket in triples {
            //         match bucket.hash {
            //             &0u64 => { // empty or in place
            //                 // swapping = false;
            //                 // swap_items = items.clone();
            //                 // swap_triples = triples.clone();
            //             }
            //             &full_hash => {
            //                 // Put it where it would have been
            //                 // let half_off = (cap >> table::LOG2_CHUNK) as int;
            //                 // let (hsh2, key2, val2) = (
            //                 //     (hsh as *mut u64 as *mut table::TriAry<K, V>).offset(half_off) as *mut u64,
            //                 //     (key as *mut K as *mut table::TriAry<K, V>).offset(half_off) as *mut K,
            //                 //     (val as *mut V as *mut table::TriAry<K, V>).offset(half_off) as *mut V,
            //                 // );
            //                 // if last_empty && *hsh2 == 0u64 {
            //                 //     unsafe {
            //                 //         *hsh2 = hash;
            //                 //         overwrite(key2, k);
            //                 //         overwrite(val2, v);
            //                 //         // (*unsfptr).table.size = potential_new_size;
            //                 //     }
            //                 // }
            //                 // else {
            //                 // (*unsfptr).pop_internal(table::FullIndex{idx:idx as int,hash: table::SafeHash{hash:hash},nocopy: marker::NoCopy,});
            //                 // (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
            //                 // }
            //                 // last_empty = false;
            //                 //-----
            //                 if full_hash as uint & cap == cap {
            //                     let k = ptr::read(bucket.key as *mut K as *const K);
            //                     let v = ptr::read(bucket.val as *mut V as *const V);

            //                     let hash = replace(bucket.hash, 0u64);
            //                     (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
            //                     // if !swapping {
            //                     //     swapping = true;
            //                     //     // swap_items = prev_items.clone();
            //                     //     // swap_triples = prev_triples.clone();
            //                     // }
            //                 }
            //                 // else {
            //                 //     if swapping {
            //                 //         let swap_bucket = match swap_triples.next() {
            //                 //             Some(bucket) => bucket,
            //                 //             None => {
            //                 //                 swap_triples = swap_items.next().unwrap();
            //                 //                 swap_triples.next().unwrap()
            //                 //             }
            //                 //         };
            //                 //         let k = ptr::read(bucket.key as *mut K as *const K);
            //                 //         let v = ptr::read(bucket.val as *mut V as *const V);

            //                 //         *swap_bucket.hash = *bucket.hash;
            //                 //         *bucket.hash = 0u64;
            //                 //         overwrite(swap_bucket.key, k);
            //                 //         overwrite(swap_bucket.val, v);
            //                 //     } else {
            //                 //         swap_items = items.clone();
            //                 //         swap_triples = triples.clone();
            //                 //     }
            //                 // }
            //                 //-----
            //                 // if full_hash as uint & cap == cap {
            //                 //     let k = ptr::read(bucket.key as *mut K as *const K);
            //                 //     let v = ptr::read(bucket.val as *mut V as *const V);

            //                 //     let hash = replace(bucket.hash, 0u64);
            //                 //     (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:hash}, k, v, |_, _| ());
            //                 //     let mut swap_items = items.clone();
            //                 //     let mut swap_triples = triples.clone();
            //                 //     let mut idx_delta = 1;
            //                 //     let he_wants_there = full_hash as uint & (cap - 1);
            //                 //     loop {
            //                 //         let swap_bucket = match swap_triples.next() {
            //                 //             Some(bucket) => bucket,
            //                 //             None => {
            //                 //                 swap_triples = match swap_items.next() {
            //                 //                     Some(t) => t,
            //                 //                     None => break
            //                 //                 };
            //                 //                 swap_triples.next().unwrap()
            //                 //             }
            //                 //         };
            //                 //         match swap_bucket.hash {
            //                 //             &0u64 => break,
            //                 //             &swap_full_hash => {
            //                 //                 if swap_full_hash as uint & cap == cap {
            //                 //                     continue
            //                 //                 }
            //                 //                 else {
            //                 //                     let k = ptr::read(swap_bucket.key as *mut K as *const K);
            //                 //                     let v = ptr::read(swap_bucket.val as *mut V as *const V);
            //                 //                     *bucket.hash = replace(swap_bucket.hash, 0u64);
            //                 //                     overwrite(bucket.key, k);
            //                 //                     overwrite(bucket.val, v);
            //                 //                     break
            //                 //                 }
            //                 //             }
            //                 //         }
            //                 //     }
            //                 // }
            //                 // else {
            //                 //     if swapping {
            //                 //         let swap_bucket = match swap_triples.next() {
            //                 //             Some(bucket) => bucket,
            //                 //             None => {
            //                 //                 swap_triples = swap_items.next().unwrap();
            //                 //                 swap_triples.next().unwrap()
            //                 //             }
            //                 //         };
            //                 //         let k = ptr::read(bucket.key as *mut K as *const K);
            //                 //         let v = ptr::read(bucket.val as *mut V as *const V);

            //                 //         *swap_bucket.hash = *bucket.hash;
            //                 //         *bucket.hash = 0u64;
            //                 //         overwrite(swap_bucket.key, k);
            //                 //         overwrite(swap_bucket.val, v);
            //                 //     }
            //                 // }
            //             }
            //         }
            //         // idx += 1;
            //     // }
            // }
        }
        assert_eq!(self.table.size(), old_size);
    }

    /// Performs any necessary resize operations, such that there's space for
    /// new_size elements.
    fn make_some_room(&mut self, new_size: uint) {
        let (grow_at, shrink_at) = self.resize_policy.capacity_range(new_size);
        let cap = self.table.capacity();

        // An invalid value shouldn't make us run out of space.
        debug_assert!(grow_at >= new_size);

        // println!("[{}, {}] cap:{}", grow_at, shrink_at, cap)
        if cap <= grow_at {
            let new_capacity = max(cap << 1, INITIAL_CAPACITY);
            if !self.table.try_grow(new_capacity >> table::LOG2_CHUNK) {
                self.resize(new_capacity);
                return;
            }
            self.resize_inplace(cap, new_capacity);
        } else if shrink_at <= cap {
            let new_capacity = cap >> 1;
            // let keep_len = self.table.size;
            unsafe {
                let mut items = table::TriAryIter::new(self.table.as_mut_slice().mut_slice_from(new_capacity >> table::LOG2_CHUNK));
                let unsfptr = unsafe{self as *mut HashMap<K, V, H>};
                (*unsfptr).table.cap = new_capacity >> table::LOG2_CHUNK;

                for mut triples in items {
                    for bucket in triples {
                        match bucket.hash {
                            &0u64 => {}
                            &full_hash => {
                                let k = ptr::read(bucket.key as *mut K as *const K);
                                let v = ptr::read(bucket.val as *mut V as *const V);
                                (*unsfptr).overwrite_hashed_existing_with(table::SafeHash{hash:full_hash}, k, v, |_, _| ());
                                *bucket.hash = 0u64;
                            }
                        }
                    }
                }
            }
            self.table.shrink_to(new_capacity);
            // self.table.size = keep_len;
        }
    }

    /// Perform robin hood bucket stealing at the given 'index'. You must
    /// also pass that probe's "distance to initial bucket" so we don't have
    /// to recalculate it, as well as the total number of probes already done
    /// so we have some sort of upper bound on the number of probes to do.
    ///
    /// 'hash', 'k', and 'v' are the elements to robin hood into the hashtable.
    fn robin_hood(&mut self, mut index: table::FullIndex, mut dib_param: uint,
                  mut hash: table::SafeHash, mut k: K, mut v: V) {
        #![inline(always)]
        let (mut hash_ref, mut key_ref, mut val_ref) = self.table.ptr_mut_idx(index.raw_index() as int);

        'outer: loop { unsafe {
            let (old_hash, old_key, old_val) = {
                // let (old_hash_ref, old_key_ref, old_val_ref) =
                //         self.table.read_all_mut(&index);

                let old_hash = replace(&mut *(hash_ref as *mut table::SafeHash), hash);
                let old_key  = replace(&mut *key_ref,  k);
                let old_val  = replace(&mut *val_ref,  v);

                (old_hash, old_key, old_val)
            };

            let mut probe = self.probe_next(index.raw_index());

            for dib in range(dib_param + 1, self.table.size()) {
                let (hr, kr, vr) = self.table.ptr_mut_idx(probe as int); // TODO uint only?

                let full_index = match self.table.internal_peek(probe, *hr) {
                    table::Empty(idx) => {
                        // Finally. A hole!
                        self.table.put(idx, old_hash, old_key, old_val);
                        return;
                    },
                    table::Full(idx) => idx
                };

                let probe_dib = self.bucket_distance(&full_index);

                // Robin hood! Steal the spot.
                if probe_dib < dib {
                    hash_ref = hr;
                    key_ref = kr;
                    val_ref = vr;
                    index = full_index;
                    dib_param = probe_dib;
                    hash = old_hash;
                    k = old_key;
                    v = old_val;
                    continue 'outer;
                }

                probe = self.probe_next(probe);
            }

            // println!("{} {} {}", index.raw_index(), dib_param, hash.inspect());
            fail!("HashMap fatal error: 100% load factor?");
        }}
    }

    /// Inserts an element which has already been hashed, returning a reference
    /// to that element inside the hashtable. This is more efficient that using
    /// `insert`, since the key will not be rehashed.
    fn insert_hashed<'a>(&'a mut self, hash: table::SafeHash, k: K, v: V) -> &'a mut V {
        let mut potential_new_size = self.table.len + 1;
        self.make_some_room(potential_new_size);
        let retval = self.overwrite_hashed_existing_with(hash, k, v, |_, _| potential_new_size -= 1);
        self.table.len = potential_new_size;
        retval
    }

    /// Return the value corresponding to the key in the map, or insert
    /// and return the value if it doesn't exist.
    pub fn find_or_insert<'a>(&'a mut self, k: K, v: V) -> &'a mut V {
        self.find_with_or_insert_with(k, v, |_k, _v, _a| (), |_k, a| a)
    }

    /// Return the value corresponding to the key in the map, or create,
    /// insert, and return a new value if it doesn't exist.
    pub fn find_or_insert_with<'a>(&'a mut self, k: K, f: |&K| -> V)
                               -> &'a mut V {
        self.find_with_or_insert_with(k, (), |_k, _v, _a| (), |k, _a| f(k))
    }

    /// Insert a key-value pair into the map if the key is not already present.
    /// Otherwise, modify the existing value for the key.
    /// Returns the new or modified value for the key.
    pub fn insert_or_update_with<'a>(
                                 &'a mut self,
                                 k: K,
                                 v: V,
                                 f: |&K, &mut V|)
                                 -> &'a mut V {
        self.find_with_or_insert_with(k, v, |k, v, _a| f(k, v), |_k, a| a)
    }

    /// Modify and return the value corresponding to the key in the map, or
    /// insert and return a new value if it doesn't exist.
    ///
    /// This method allows for all insertion behaviours of a hashmap;
    /// see methods like `insert`, `find_or_insert` and
    /// `insert_or_update_with` for less general and more friendly
    /// variations of this.
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::collections::HashMap;
    ///
    /// // map some strings to vectors of strings
    /// let mut map = HashMap::new();
    /// map.insert("a key", vec!["value"]);
    /// map.insert("z key", vec!["value"]);
    ///
    /// let new = vec!["a key", "b key", "z key"];
    ///
    /// for k in new.move_iter() {
    ///     map.find_with_or_insert_with(
    ///         k, "new value",
    ///         // if the key does exist either prepend or append this
    ///         // new value based on the first letter of the key.
    ///         |key, already, new| {
    ///             if key.as_slice().starts_with("z") {
    ///                 already.unshift(new);
    ///             } else {
    ///                 already.push(new);
    ///             }
    ///         },
    ///         // if the key doesn't exist in the map yet, add it in
    ///         // the obvious way.
    ///         |_k, v| vec![v]);
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// assert_eq!(map.get(&"a key"), &vec!["value", "new value"]);
    /// assert_eq!(map.get(&"b key"), &vec!["new value"]);
    /// assert_eq!(map.get(&"z key"), &vec!["new value", "value"]);
    /// ```
    pub fn find_with_or_insert_with<'a, A>(&'a mut self,
                                           k: K,
                                           a: A,
                                           found: |&K, &mut V, A|,
                                           not_found: |&K, A| -> V)
                                          -> &'a mut V {
        let hash = self.make_hash(&k);
        match self.search_hashed(&hash, &k) {
            None => {
                let v = not_found(&k, a);
                self.insert_hashed(hash, k, v)
            },
            Some(idx) => {
                let (_, v_ref) = self.table.read_mut(&idx);
                found(&k, v_ref, a);
                v_ref
            }
        }
    }

    /// Retrieves a value for the given key, failing if the key is not present.
    pub fn get<'a>(&'a self, k: &K) -> &'a V {
        match self.find(k) {
            Some(v) => v,
            None => fail!("no entry found for key")
        }
    }

    /// Retrieves a (mutable) value for the given key, failing if the key is not present.
    pub fn get_mut<'a>(&'a mut self, k: &K) -> &'a mut V {
        match self.find_mut(k) {
            Some(v) => v,
            None => fail!("no entry found for key")
        }
    }

    /// Return true if the map contains a value for the specified key,
    /// using equivalence.
    pub fn contains_key_equiv<Q: Hash<S> + Equiv<K>>(&self, key: &Q) -> bool {
        self.search_equiv(key).is_some()
    }

    /// Return the value corresponding to the key in the map, using
    /// equivalence.
    pub fn find_equiv<'a, Q: Hash<S> + Equiv<K>>(&'a self, k: &Q) -> Option<&'a V> {
        match self.search_equiv(k) {
            None      => None,
            Some(idx) => {
                let (_, v_ref) = self.table.read(&idx);
                Some(v_ref)
            }
        }
    }

    /// An iterator visiting all keys in arbitrary order.
    /// Iterator element type is &'a K.
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        self.iter().map(|(k, _v)| k)
    }

    /// An iterator visiting all values in arbitrary order.
    /// Iterator element type is &'a V.
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        self.iter().map(|(_k, v)| v)
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// Iterator element type is (&'a K, &'a V).
    pub fn iter<'a>(&'a self) -> Entries<'a, K, V> {
        self.table.iter()
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    /// Iterator element type is (&'a K, &'a mut V).
    pub fn mut_iter<'a>(&'a mut self) -> MutEntries<'a, K, V> {
        self.table.mut_iter()
    }

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    pub fn move_iter(self) -> MoveEntries<K, V> {
        self.table.move_iter().map(|(_, k, v)| (k, v))
    }
}

impl<K: Eq + Hash<S>, V: Clone, S, H: Hasher<S>> HashMap<K, V, H> {
    /// Like `find`, but returns a copy of the value.
    pub fn find_copy(&self, k: &K) -> Option<V> {
        self.find(k).map(|v| (*v).clone())
    }

    /// Like `get`, but returns a copy of the value.
    pub fn get_copy(&self, k: &K) -> V {
        (*self.get(k)).clone()
    }
}

impl<K: Eq + Hash<S>, V: PartialEq, S, H: Hasher<S>> PartialEq for HashMap<K, V, H> {
    fn eq(&self, other: &HashMap<K, V, H>) -> bool {
        if self.len() != other.len() { return false; }

        self.iter()
          .all(|(key, value)| {
            match other.find(key) {
                None    => false,
                Some(v) => *value == *v
            }
        })
    }
}

// impl<K: Eq + Hash<S> + Show, V: Show, S, H: Hasher<S>> Show for HashMap<K, V, H> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         try!(write!(f, r"\{"));

//         for (i, (k, v)) in self.iter().enumerate() {
//             if i != 0 { try!(write!(f, ", ")); }
//             try!(write!(f, "{}: {}", *const K, *const V));
//         }

//         write!(f, r"\}")
//     }
// }

//debug
impl<K: Eq + Hash<S>, V, S, H: Hasher<S>> Show for HashMap<K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}: {:?}", *k, *v));
        }

        write!(f, "}}")
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S> + Default> Default for HashMap<K, V, H> {
    fn default() -> HashMap<K, V, H> {
        HashMap::with_hasher(Default::default())
    }
}

/// HashMap iterator
pub type Entries<'a, K, V> = table::Entries<'a, K, V>;

/// HashMap mutable values iterator
pub type MutEntries<'a, K, V> = table::MutEntries<'a, K, V>;

/// HashMap move iterator
pub type MoveEntries<K, V> =
    iter::Map<'static, (table::SafeHash, K, V), (K, V), table::MoveEntries<K, V>>;

/// HashMap keys iterator
pub type Keys<'a, K, V> =
    iter::Map<'static, (&'a K, &'a V), &'a K, Entries<'a, K, V>>;

/// HashMap values iterator
pub type Values<'a, K, V> =
    iter::Map<'static, (&'a K, &'a V), &'a V, Entries<'a, K, V>>;

impl<K: Eq + Hash<S>, V, S, H: Hasher<S> + Default> FromIterator<(K, V)> for HashMap<K, V, H> {
    fn from_iter<T: Iterator<(K, V)>>(iter: T) -> HashMap<K, V, H> {
        let (lower, _) = iter.size_hint();
        let mut map = HashMap::with_capacity_and_hasher(lower, Default::default());
        map.extend(iter);
        map
    }
}

impl<K: Eq + Hash<S>, V, S, H: Hasher<S> + Default> Extendable<(K, V)> for HashMap<K, V, H> {
    fn extend<T: Iterator<(K, V)>>(&mut self, mut iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

/// HashSet iterator
pub type SetItems<'a, K> =
    iter::Map<'static, (&'a K, &'a ()), &'a K, Entries<'a, K, ()>>;

/// HashSet move iterator
pub type SetMoveItems<K> =
    iter::Map<'static, (K, ()), K, MoveEntries<K, ()>>;

/// An implementation of a hash set using the underlying representation of a
/// HashMap where the value is (). As with the `HashMap` type, a `HashSet`
/// requires that the elements implement the `Eq` and `Hash` traits.
#[deriving(Clone)]
pub struct HashSet<T, H = sip::SipHasher> {
    map: HashMap<T, (), H>
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> PartialEq for HashSet<T, H> {
    fn eq(&self, other: &HashSet<T, H>) -> bool {
        if self.len() != other.len() { return false; }

        self.iter().all(|key| other.contains(key))
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> Eq for HashSet<T, H> {}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> Collection for HashSet<T, H> {
    fn len(&self) -> uint { self.map.len() }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> Mutable for HashSet<T, H> {
    fn clear(&mut self) { self.map.clear() }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> Set<T> for HashSet<T, H> {
    fn contains(&self, value: &T) -> bool { self.map.contains_key(value) }

    fn is_disjoint(&self, other: &HashSet<T, H>) -> bool {
        self.iter().all(|v| !other.contains(v))
    }

    fn is_subset(&self, other: &HashSet<T, H>) -> bool {
        self.iter().all(|v| other.contains(v))
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> MutableSet<T> for HashSet<T, H> {
    fn insert(&mut self, value: T) -> bool { self.map.insert(value, ()) }

    fn remove(&mut self, value: &T) -> bool { self.map.remove(value) }
}

impl<T: Hash + Eq> HashSet<T, sip::SipHasher> {
    /// Create an empty HashSet
    pub fn new() -> HashSet<T, sip::SipHasher> {
        HashSet::with_capacity(INITIAL_CAPACITY)
    }

    /// Create an empty HashSet with space for at least `n` elements in
    /// the hash table.
    pub fn with_capacity(capacity: uint) -> HashSet<T, sip::SipHasher> {
        HashSet { map: HashMap::with_capacity(capacity) }
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> HashSet<T, H> {
    /// Creates a new empty hash set which will use the given hasher to hash
    /// keys.
    ///
    /// The hash set is also created with the default initial capacity.
    pub fn with_hasher(hasher: H) -> HashSet<T, H> {
        HashSet::with_capacity_and_hasher(INITIAL_CAPACITY, hasher)
    }

    /// Create an empty HashSet with space for at least `capacity`
    /// elements in the hash table, using `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow `HashSet`s to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    pub fn with_capacity_and_hasher(capacity: uint, hasher: H) -> HashSet<T, H> {
        HashSet { map: HashMap::with_capacity_and_hasher(capacity, hasher) }
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S>> HashSet<T, H> {
    /// Reserve space for at least `n` elements in the hash table.
    pub fn reserve(&mut self, n: uint) {
        self.map.reserve(n)
    }

    /// Returns true if the hash set contains a value equivalent to the
    /// given query value.
    pub fn contains_equiv<Q: Hash<S> + Equiv<T>>(&self, value: &Q) -> bool {
      self.map.contains_key_equiv(value)
    }

    /// An iterator visiting all elements in arbitrary order.
    /// Iterator element type is &'a T.
    pub fn iter<'a>(&'a self) -> SetItems<'a, T> {
        self.map.keys()
    }

    /// Creates a consuming iterator, that is, one that moves each value out
    /// of the set in arbitrary order. The set cannot be used after calling
    /// this.
    pub fn move_iter(self) -> SetMoveItems<T> {
        self.map.move_iter().map(|(k, _)| k)
    }

    /// Visit the values representing the difference
    pub fn difference<'a>(&'a self, other: &'a HashSet<T, H>) -> SetAlgebraItems<'a, T, H> {
        Repeat::new(other).zip(self.iter())
            .filter_map(|(other, elt)| {
                if !other.contains(elt) { Some(elt) } else { None }
            })
    }

    /// Visit the values representing the symmetric difference
    pub fn symmetric_difference<'a>(&'a self, other: &'a HashSet<T, H>)
        -> Chain<SetAlgebraItems<'a, T, H>, SetAlgebraItems<'a, T, H>> {
        self.difference(other).chain(other.difference(self))
    }

    /// Visit the values representing the intersection
    pub fn intersection<'a>(&'a self, other: &'a HashSet<T, H>)
        -> SetAlgebraItems<'a, T, H> {
        Repeat::new(other).zip(self.iter())
            .filter_map(|(other, elt)| {
                if other.contains(elt) { Some(elt) } else { None }
            })
    }

    /// Visit the values representing the union
    pub fn union<'a>(&'a self, other: &'a HashSet<T, H>)
        -> Chain<SetItems<'a, T>, SetAlgebraItems<'a, T, H>> {
        self.iter().chain(other.difference(self))
    }
}

impl<T: Eq + Hash<S> + fmt::Show, S, H: Hasher<S>> fmt::Show for HashSet<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, x) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{}", *x));
        }

        write!(f, "}}")
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S> + Default> FromIterator<T> for HashSet<T, H> {
    fn from_iter<I: Iterator<T>>(iter: I) -> HashSet<T, H> {
        let (lower, _) = iter.size_hint();
        let mut set = HashSet::with_capacity_and_hasher(lower, Default::default());
        set.extend(iter);
        set
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S> + Default> Extendable<T> for HashSet<T, H> {
    fn extend<I: Iterator<T>>(&mut self, mut iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

impl<T: Eq + Hash<S>, S, H: Hasher<S> + Default> Default for HashSet<T, H> {
    fn default() -> HashSet<T, H> {
        HashSet::with_hasher(Default::default())
    }
}

// `Repeat` is used to feed the filter closure an explicit capture
// of a reference to the other set
/// Set operations iterator
pub type SetAlgebraItems<'a, T, H> =
    FilterMap<'static, (&'a HashSet<T, H>, &'a T), &'a T,
              Zip<Repeat<&'a HashSet<T, H>>, SetItems<'a, T>>>;

#[cfg(test)]
mod test_map {
    use prelude::*;

    use super::HashMap;
    use cmp::Equiv;
    use hash;
    use iter::{Iterator,range_inclusive,range_step_inclusive};
    use cell::RefCell;

    struct KindaIntLike(int);

    impl Equiv<int> for KindaIntLike {
        fn equiv(&self, other: &int) -> bool {
            let KindaIntLike(this) = *self;
            this == *other
        }
    }
    impl<S: hash::Writer> hash::Hash<S> for KindaIntLike {
        fn hash(&self, state: &mut S) {
            let KindaIntLike(this) = *self;
            this.hash(state)
        }
    }

    #[test]
    fn test_create_capacity_zero() {
        let mut m = HashMap::with_capacity(0u);

        assert!(m.insert(1i, 1i));
        // println!("{:?}", m);
        // println!("{}", m.table.chunks);

        assert!(m.contains_key(&1));
        assert!(!m.contains_key(&0));
    }

    #[test]
    fn test_insert() {
        let mut m = HashMap::new();
        assert_eq!(m.len(), 0);
        assert!(m.insert(1i, 2i));
        assert_eq!(m.len(), 1);
        assert!(m.insert(2i, 4i));
        assert_eq!(m.len(), 2);
        assert_eq!(*m.find(&1).unwrap(), 2);
        assert_eq!(*m.find(&2).unwrap(), 4);
    }

    local_data_key!(drop_vector: RefCell<Vec<int>>)

    #[deriving(Hash, PartialEq, Eq)]
    struct Dropable {
        k: uint
    }


    impl Dropable {
        fn new(k: uint) -> Dropable {
            let v = drop_vector.get().unwrap();
            v.borrow_mut().as_mut_slice()[k] += 1;

            Dropable { k: k }
        }
    }

    impl Drop for Dropable {
        fn drop(&mut self) {
            let v = drop_vector.get().unwrap();
            v.borrow_mut().as_mut_slice()[self.k] -= 1;
        }
    }

    #[test]
    fn test_drops() {
        drop_vector.replace(Some(RefCell::new(Vec::from_elem(200, 0i))));

        {
            let mut m = HashMap::new();

            let v = drop_vector.get().unwrap();
            for i in range(0u, 200) {
                assert_eq!(v.borrow().as_slice()[i], 0);
            }
            drop(v);

            for i in range(0u, 100) {
                let d1 = Dropable::new(i);
                let d2 = Dropable::new(i+100);
                m.insert(d1, d2);
            }

            let v = drop_vector.get().unwrap();
            for i in range(0u, 200) {
                assert_eq!(v.borrow().as_slice()[i], 1);
            }
            drop(v);

            for i in range(0u, 50) {
                let k = Dropable::new(i);
                let v = m.pop(&k);

                println!("{}", i);
                assert!(v.is_some());

                let v = drop_vector.get().unwrap();
                assert_eq!(v.borrow().as_slice()[i], 1);
                assert_eq!(v.borrow().as_slice()[i+100], 1);
            }

            let v = drop_vector.get().unwrap();
            for i in range(0u, 50) {
                assert_eq!(v.borrow().as_slice()[i], 0);
                assert_eq!(v.borrow().as_slice()[i+100], 0);
            }

            for i in range(50u, 100) {
                assert_eq!(v.borrow().as_slice()[i], 1);
                assert_eq!(v.borrow().as_slice()[i+100], 1);
            }
        }

        let v = drop_vector.get().unwrap();
        for i in range(0u, 200) {
            assert_eq!(v.borrow().as_slice()[i], 0);
        }
    }

    #[test]
    fn test_empty_pop() {
        let mut m: HashMap<int, bool> = HashMap::new();
        assert_eq!(m.pop(&0), None);
    }

    #[test]
    fn test_lots_of_insertions() {
        let mut m = HashMap::new();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in range(0i, 10) {
            assert!(m.is_empty());

            for i in range_inclusive(1i, 1000) {
                // let old_m = m.clone();
                assert!(m.insert(i, i));

                let b = {
                    let mut v = Vec::new();
                    for j in range_inclusive(1, i) {
                        let r = m.find(&j);
                        v.push(r);
                        // if r.is_none() {
                            // println!("{}", m);
                        // }
                        // assert_eq!((r, i), (Some(&j), i));
                    }
                    let b = v.iter().enumerate().all(|(i, &e)| {e.map(|&e| e) == Some((i + 1) as int)});
                    if !b {
                        println!("{}", v);
                    }
                    b
                };
                // if !b {

    {
        let cap = m.table.capacity();
        // let mut triples = items.next().unwrap();
        // let unsfptr = unsafe{self as *HashMap<K, V, H> as *mut HashMap<K, V, H>};
        let mut items = unsafe{super::table::TriAryIter::new(m.table.as_mut_slice())};
        // (*unsfptr).table.set_len(new_capacity >> table::LOG2_CHUNK);
        // let mut last_empty = false;
        // let mut cap_tz = cap.trailing_zeros();
        let mut idx = 0u;
        // let mut swapping = false;
        // let mut swap_items = items.clone();
        // let mut swap_triples = mem::uninit();

        // println!("has {} spots:", cap);
        // let mut v = Vec::new();
        // for mut triples in items {
        //     for bucket in triples {
        //         match bucket.hash {
        //             &0u64 => v.push(None),
        //             &full_hash => {
        //                 v.push(Some((full_hash as uint & (cap - 1), bucket.key, bucket.val)));
        //             }
        //         }
        //     }
        //     println!("{}", v);
        //     v.clear();
        // }
    }
    // println!("{}", m);
                    // println!("good {}", old_m);
                // }
                assert!(b);

                for j in range_inclusive(i+1, 1000) {
                    let r = m.find(&j);
                    assert_eq!(r, None);
                }
            }

            for i in range_inclusive(1001i, 2000) {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in range_inclusive(1i, 1000) {
                assert!(m.remove(&i));

                for j in range_inclusive(1, i) {
                    assert!(!m.contains_key(&j));
                }

                for j in range_inclusive(i+1, 1000) {
                    assert!(m.contains_key(&j));
                }
            }

            for i in range_inclusive(1i, 1000) {
                assert!(!m.contains_key(&i));
            }

            for i in range_inclusive(1i, 1000) {
                assert!(m.insert(i, i));
            }

            // remove backwards
            for i in range_step_inclusive(1000i, 1, -1) {
                assert!(m.remove(&i));

                for j in range_inclusive(i, 1000) {
                    assert!(!m.contains_key(&j));
                }

                for j in range_inclusive(1, i-1) {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }

    #[test]
    fn test_find_mut() {
        let mut m = HashMap::new();
        assert!(m.insert(1i, 12i));
        assert!(m.insert(2i, 8i));
        assert!(m.insert(5i, 14i));
        let new = 100;
        match m.find_mut(&5) {
            None => fail!(), Some(x) => *x = new
        }
        assert_eq!(m.find(&5), Some(&new));
    }

    #[test]
    fn test_insert_overwrite() {
        let mut m = HashMap::new();
        assert!(m.insert(1i, 2i));
        assert_eq!(*m.find(&1).unwrap(), 2);
        assert!(!m.insert(1i, 3i));
        assert_eq!(*m.find(&1).unwrap(), 3);
    }

    #[test]
    fn test_insert_conflicts() {
        let mut m = HashMap::with_capacity(4);
        assert!(m.insert(1i, 2i));
        assert!(m.insert(5i, 3i));
        assert!(m.insert(9i, 4i));
        assert_eq!(*m.find(&9).unwrap(), 4);
        assert_eq!(*m.find(&5).unwrap(), 3);
        assert_eq!(*m.find(&1).unwrap(), 2);
    }

    #[test]
    fn test_conflict_remove() {
        let mut m = HashMap::with_capacity(4);
        assert!(m.insert(1i, 2i));
        assert_eq!(*m.find(&1).unwrap(), 2);
        assert!(m.insert(5, 3));
        assert_eq!(*m.find(&1).unwrap(), 2);
        assert_eq!(*m.find(&5).unwrap(), 3);
        assert!(m.insert(9, 4));
        assert_eq!(*m.find(&1).unwrap(), 2);
        assert_eq!(*m.find(&5).unwrap(), 3);
        assert_eq!(*m.find(&9).unwrap(), 4);
        assert!(m.remove(&1));
        assert_eq!(*m.find(&9).unwrap(), 4);
        assert_eq!(*m.find(&5).unwrap(), 3);
    }

    #[test]
    fn test_is_empty() {
        let mut m = HashMap::with_capacity(4);
        assert!(m.insert(1i, 2i));
        assert!(!m.is_empty());
        assert!(m.remove(&1));
        assert!(m.is_empty());
    }

    #[test]
    fn test_pop() {
        let mut m = HashMap::new();
        m.insert(1i, 2i);
        assert_eq!(m.pop(&1), Some(2));
        assert_eq!(m.pop(&1), None);
    }

    #[test]
    #[allow(experimental)]
    fn test_pop_equiv() {
        let mut m = HashMap::new();
        m.insert(1i, 2i);
        assert_eq!(m.pop_equiv(&KindaIntLike(1)), Some(2));
        assert_eq!(m.pop_equiv(&KindaIntLike(1)), None);
    }

    #[test]
    fn test_swap() {
        let mut m = HashMap::new();
        assert_eq!(m.swap(1i, 2i), None);
        assert_eq!(m.swap(1i, 3i), Some(2));
        assert_eq!(m.swap(1i, 4i), Some(3));
    }

    #[test]
    fn test_move_iter() {
        let hm = {
            let mut hm = HashMap::new();

            hm.insert('a', 1i);
            hm.insert('b', 2i);

            hm
        };

        let v = hm.move_iter().collect::<Vec<(char, int)>>();
        assert!([('a', 1), ('b', 2)] == v.as_slice() || [('b', 2), ('a', 1)] == v.as_slice());
    }

    #[test]
    fn test_iterate() {
        let mut m = HashMap::with_capacity(4);
        for i in range(0u, 32) {
            assert!(m.insert(i, i*2));
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        for (k, v) in m.iter() {
            assert_eq!(*v, *k * 2);
            observed |= 1 << *k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_keys() {
        let vec = vec![(1i, 'a'), (2i, 'b'), (3i, 'c')];
        let map = vec.move_iter().collect::<HashMap<int, char>>();
        let keys = map.keys().map(|&k| k).collect::<Vec<int>>();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = vec![(1i, 'a'), (2i, 'b'), (3i, 'c')];
        let map = vec.move_iter().collect::<HashMap<int, char>>();
        let values = map.values().map(|&v| v).collect::<Vec<char>>();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_find() {
        let mut m = HashMap::new();
        assert!(m.find(&1i).is_none());
        m.insert(1i, 2i);
        match m.find(&1) {
            None => fail!(),
            Some(v) => assert_eq!(*v, 2)
        }
    }

    #[test]
    fn test_eq() {
        let mut m1 = HashMap::new();
        m1.insert(1i, 2i);
        m1.insert(2i, 3i);
        m1.insert(3i, 4i);

        let mut m2 = HashMap::new();
        m2.insert(1i, 2i);
        m2.insert(2i, 3i);

        assert!(m1 != m2);

        m2.insert(3i, 4i);

        assert_eq!(m1, m2);
    }

    #[test]
    fn test_show() {
        let mut map: HashMap<int, int> = HashMap::new();
        let empty: HashMap<int, int> = HashMap::new();

        map.insert(1i, 2i);
        map.insert(3i, 4i);

        let map_str = format!("{}", map);

        assert!(map_str == "{1: 2, 3: 4}".to_string() || map_str == "{3: 4, 1: 2}".to_string());
        assert_eq!(format!("{}", empty), "{}".to_string());
    }

    #[test]
    fn test_expand() {
        let mut m = HashMap::new();

        assert_eq!(m.len(), 0);
        assert!(m.is_empty());

        let mut i = 0u;
        let old_cap = m.table.capacity();
        while old_cap == m.table.capacity() {
            m.insert(i, i);
            i += 1;
        }

        assert_eq!(m.len(), i);
        assert!(!m.is_empty());
    }

    #[test]
    fn test_find_equiv() {
        let mut m = HashMap::new();

        let (foo, bar, baz) = (1i,2i,3i);
        m.insert("foo".to_string(), foo);
        m.insert("bar".to_string(), bar);
        m.insert("baz".to_string(), baz);


        assert_eq!(m.find_equiv(&("foo")), Some(&foo));
        assert_eq!(m.find_equiv(&("bar")), Some(&bar));
        assert_eq!(m.find_equiv(&("baz")), Some(&baz));

        assert_eq!(m.find_equiv(&("qux")), None);
    }

    #[test]
    fn test_from_iter() {
        let xs = [(1i, 1i), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

        for &(k, v) in xs.iter() {
            assert_eq!(map.find(&k), Some(&v));
        }
    }

    #[test]
    fn test_size_hint() {
        let xs = [(1i, 1i), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_mut_size_hint() {
        let xs = [(1i, 1i), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let mut map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

        let mut iter = map.mut_iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_resize_policy() {
        let mut m = HashMap::new();

        assert_eq!(m.len(), 0);
        assert_eq!(m.table.capacity(), 0);
        assert!(m.is_empty());

        m.insert(0, 0);
        m.remove(&0);
        let initial_cap = m.table.capacity();
        m.reserve(initial_cap * 2);
        let cap = m.table.capacity();

        assert_eq!(cap, initial_cap * 2);

        let mut i = 0u;
        for _ in range(0, cap * 3 / 4) {
            m.insert(i, i);
            i += 1;
        }

        assert_eq!(m.len(), i);
        assert_eq!(m.table.capacity(), cap);

        for _ in range(0, cap / 4) {
            m.insert(i, i);
            i += 1;
        }

        let new_cap = m.table.capacity();
        assert_eq!(new_cap, cap * 2);

        for _ in range(0, cap / 2) {
            i -= 1;
            m.remove(&i);
            println!("{} {}", i, m.len());
            assert_eq!(m.table.capacity(), new_cap);
        }

        for _ in range(0, cap / 2 - 1) {
            i -= 1;
            m.remove(&i);
            println!("{} {}", i, m.len());
        }

        assert_eq!(m.len(), i);
        assert!(!m.is_empty());
        assert_eq!(m.table.capacity(), cap);
    }
}

#[cfg(test)]
mod test_set {
    use prelude::*;

    use super::HashSet;
    use collections::Collection;
    use slice::ImmutableEqVector;

    #[test]
    fn test_disjoint() {
        let mut xs = HashSet::new();
        let mut ys = HashSet::new();
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(5i));
        assert!(ys.insert(11i));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(7));
        assert!(xs.insert(19));
        assert!(xs.insert(4));
        assert!(ys.insert(2));
        assert!(ys.insert(-11));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(ys.insert(7));
        assert!(!xs.is_disjoint(&ys));
        assert!(!ys.is_disjoint(&xs));
    }

    #[test]
    fn test_subset_and_superset() {
        let mut a = HashSet::new();
        assert!(a.insert(0i));
        assert!(a.insert(5));
        assert!(a.insert(11));
        assert!(a.insert(7));

        let mut b = HashSet::new();
        assert!(b.insert(0i));
        assert!(b.insert(7));
        assert!(b.insert(19));
        assert!(b.insert(250));
        assert!(b.insert(11));
        assert!(b.insert(200));

        assert!(!a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(!b.is_superset(&a));

        assert!(b.insert(5));

        assert!(a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
    }

    #[test]
    fn test_iterate() {
        let mut a = HashSet::new();
        for i in range(0u, 32) {
            assert!(a.insert(i));
        }
        let mut observed: u32 = 0;
        for k in a.iter() {
            observed |= 1 << *k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_intersection() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        assert!(a.insert(11i));
        assert!(a.insert(1));
        assert!(a.insert(3));
        assert!(a.insert(77));
        assert!(a.insert(103));
        assert!(a.insert(5));
        assert!(a.insert(-5));

        assert!(b.insert(2i));
        assert!(b.insert(11));
        assert!(b.insert(77));
        assert!(b.insert(-9));
        assert!(b.insert(-42));
        assert!(b.insert(5));
        assert!(b.insert(3));

        let mut i = 0;
        let expected = [3, 5, 11, 77];
        for x in a.intersection(&b) {
            assert!(expected.contains(x));
            i += 1
        }
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_difference() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        assert!(a.insert(1i));
        assert!(a.insert(3));
        assert!(a.insert(5));
        assert!(a.insert(9));
        assert!(a.insert(11));

        assert!(b.insert(3i));
        assert!(b.insert(9));

        let mut i = 0;
        let expected = [1, 5, 11];
        for x in a.difference(&b) {
            assert!(expected.contains(x));
            i += 1
        }
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_symmetric_difference() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        assert!(a.insert(1i));
        assert!(a.insert(3));
        assert!(a.insert(5));
        assert!(a.insert(9));
        assert!(a.insert(11));

        assert!(b.insert(-2i));
        assert!(b.insert(3));
        assert!(b.insert(9));
        assert!(b.insert(14));
        assert!(b.insert(22));

        let mut i = 0;
        let expected = [-2, 1, 5, 11, 14, 22];
        for x in a.symmetric_difference(&b) {
            assert!(expected.contains(x));
            i += 1
        }
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_union() {
        let mut a = HashSet::new();
        let mut b = HashSet::new();

        assert!(a.insert(1i));
        assert!(a.insert(3));
        assert!(a.insert(5));
        assert!(a.insert(9));
        assert!(a.insert(11));
        assert!(a.insert(16));
        assert!(a.insert(19));
        assert!(a.insert(24));

        assert!(b.insert(-2i));
        assert!(b.insert(1));
        assert!(b.insert(5));
        assert!(b.insert(9));
        assert!(b.insert(13));
        assert!(b.insert(19));

        let mut i = 0;
        let expected = [-2, 1, 3, 5, 9, 11, 13, 16, 19, 24];
        for x in a.union(&b) {
            assert!(expected.contains(x));
            i += 1
        }
        // println!("{}", i);
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_from_iter() {
        let xs = [1i, 2, 3, 4, 5, 6, 7, 8, 9];

        let set: HashSet<int> = xs.iter().map(|&x| x).collect();

        for x in xs.iter() {
            assert!(set.contains(x));
        }
    }

    #[test]
    fn test_move_iter() {
        let hs = {
            let mut hs = HashSet::new();

            hs.insert('a');
            hs.insert('b');

            hs
        };

        let v = hs.move_iter().collect::<Vec<char>>();
        assert!(['a', 'b'] == v.as_slice() || ['b', 'a'] == v.as_slice());
    }

    #[test]
    fn test_eq() {
        // These constants once happened to expose a bug in insert().
        // I'm keeping them around to prevent a regression.
        let mut s1 = HashSet::new();

        s1.insert(1i);
        s1.insert(2);
        s1.insert(3);

        let mut s2 = HashSet::new();

        s2.insert(1i);
        s2.insert(2);

        assert!(s1 != s2);

        s2.insert(3);

        assert_eq!(s1, s2);
    }

    #[test]
    fn test_show() {
        let mut set: HashSet<int> = HashSet::new();
        let empty: HashSet<int> = HashSet::new();

        set.insert(1i);
        set.insert(2);

        let set_str = format!("{}", set);

        assert!(set_str == "{1, 2}".to_string() || set_str == "{2, 1}".to_string());
        assert_eq!(format!("{}", empty), "{}".to_string());
    }
}

#[cfg(test)]
mod bench {
    extern crate test;
    use prelude::*;

    use self::test::Bencher;
    use iter::{range_inclusive};

    #[bench]
    fn new_drop(b : &mut Bencher) {
        use super::HashMap;

        b.iter(|| {
            let m : HashMap<int, int> = HashMap::new();
            assert_eq!(m.len(), 0);
        })
    }

    #[bench]
    fn new_insert_drop(b : &mut Bencher) {
        use super::HashMap;

        b.iter(|| {
            let mut m = HashMap::new();
            m.insert(0i, 0i);
            assert_eq!(m.len(), 1);
        })
    }

    #[bench]
    fn insert(b: &mut Bencher) {
        use super::HashMap;

        let mut m = HashMap::new();

        for i in range_inclusive(1i, 1000) {
            m.insert(i, i);
        }

        let mut k = 1001;

        b.iter(|| {
            m.insert(k, k);
            k += 27;
            // k ^= k << 3;
        });
    }

    #[bench]
    fn find_existing(b: &mut Bencher) {
        use super::HashMap;

        let mut m = HashMap::new();

        for i in range_inclusive(1i, 1000) {
            m.insert(i, i);
        }

        b.iter(|| {
            for i in range_inclusive(1i, 1000) {
                m.contains_key(&i);
            }
        });
    }

    #[bench]
    fn find_nonexisting(b: &mut Bencher) {
        use super::HashMap;

        let mut m = HashMap::new();

        for i in range_inclusive(1i, 1000) {
            m.insert(i, i);
        }

        b.iter(|| {
            for i in range_inclusive(1001i, 2000) {
                m.contains_key(&i);
            }
        });
    }

    #[bench]
    fn hashmap_as_queue(b: &mut Bencher) {
        use super::HashMap;

        let mut m = HashMap::new();

        for i in range_inclusive(1i, 1000) {
            m.insert(i, i);
        }

        let mut k = 1i;

        b.iter(|| {
            m.pop(&k);
            m.insert(k + 1000, k + 1000);
            k += 1;
        });
    }

    #[bench]
    fn find_pop_insert(b: &mut Bencher) {
        use super::HashMap;

        let mut m = HashMap::new();

        for i in range_inclusive(1i, 1000) {
            m.insert(i, i);
        }

        let mut k = 1i;

        b.iter(|| {
            m.find(&(k + 400));
            m.find(&(k + 2000));
            m.pop(&k);
            m.insert(k + 1000, k + 1000);
            k += 1;
        })
    }

    #[bench]
    fn bench_bucket_dib(b : &mut Bencher) {
use rand::Rng;
use rand;
        use super::bucket_dib;
        let mut r = rand::task_rng();
        let h = r.gen();
        // let r1 = r.gen();

        b.iter(|| {
            for idx in range(0u, 1024) {
                test::black_box(bucket_dib(idx, h, 1024));
            }
        })
    }
}
