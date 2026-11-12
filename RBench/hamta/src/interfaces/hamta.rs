// Constants
pub const FNV_PRIME: u64 = 1099511628211;
pub const FNV_BASE: u64 = 14695981039346656037;
pub const HAMT_NODE_T_FLAG: u32 = 1;
pub const KEY_VALUE_T_FLAG: u32 = 0;
pub const CHUNK_SIZE: usize = 6;
// Type Definitions
pub type HashFn<T> = fn(&T) -> u32;
pub type EqualsFn<T> = fn(&T, &T) -> bool;
pub type StrFn<T> = fn(&T) -> String;
pub struct KeyValue<T, U> {
    pub key: T,
    pub value: U,
}
impl<T, U> KeyValue<T, U> {
}
pub enum HamtNode<T, U> {
    Leaf(Option<KeyValue<T, U>>),
    Sub(SubNode<T, U>),
}
impl<T, U> HamtNode<T, U> {
    pub fn hamt_node_search(&self, hash: u32, lvl: i32, key: &T, equals_fn: EqualsFn<T>) -> Option<&KeyValue<T, U>> {
        unimplemented!()
    }
    pub fn hamt_node_insert(&mut self, hash: u32, lvl: i32, key: T,
        value: U, hash_fn: HashFn<T>, equals_fn: EqualsFn<T>) -> (bool, Option<KeyValue<T, U>>) {
        unimplemented!()
    }
    pub fn hamt_node_remove(&mut self, hash: u32, lvl: i32, key: &T, equals_fn: EqualsFn<T>) -> Option<KeyValue<T, U>> {
        unimplemented!()
    }
    pub fn hamt_node_destroy(self) {
        unimplemented!()
    }
    pub fn hamt_node_print(&self, lvl: i32, str_fn_key: StrFn<T>, str_fn_val: StrFn<U>) {
        unimplemented!()
    }
}
pub struct SubNode<T, U> {
    pub bitmap: u32,
    pub children: Vec<HamtNode<T, U>>,
}
pub struct Hamt<T, U> {
    pub root: Option<Box<HamtNode<T, U>>>,
    pub size: i32,
    pub hash_fn: HashFn<T>,
    pub equals_fn: EqualsFn<T>,
}
impl<T, U> Hamt<T, U> {
    pub fn new_hamt(hash_fn: HashFn<T>, equals_fn: EqualsFn<T>) -> Self {
        unimplemented!()
    }
    pub fn hamt_size(&self) -> i32 {
        unimplemented!()
    }
    pub fn hamt_set(&mut self, key: &mut T, value: &mut U, conflict_kv: &mut KeyValue<&mut T, &mut U>) -> bool {
        unimplemented!()
    }
    pub fn hamt_search(&self, key: &T) -> Option<KeyValue<&T, &U>> {
        unimplemented!()
    }
    pub fn hamt_remove(&mut self, key: &T, removed_kv: &mut KeyValue<&mut T, &mut U>) -> bool {
        unimplemented!()
    }
    pub fn hamt_destroy(self, destroy_key: impl Fn(T), destroy_val: impl Fn(U)) {
        unimplemented!()
    }
    pub fn hamt_print(&self, str_fn_key: StrFn<T>, str_fn_val: StrFn<U>) {
        unimplemented!()
    }
}
// Function Declarations
pub fn hamt_int_hash<T>(key: &T) -> u32 {
    unimplemented!()
}
pub fn hamt_str_hash<T>(key: &T) -> u32 {
    unimplemented!()
}
pub fn hamt_int_equals<T>(a: &T, b: &T) -> bool {
    unimplemented!()
}
pub fn hamt_str_equals<T>(a: &T, b: &T) -> bool {
    unimplemented!()
}
pub fn hamt_fnv1_hash(key: &[u8]) -> u32 {
    unimplemented!()
}
pub fn hamt_get_symbol(hash: u32, lvl: i32) -> i32 {
    unimplemented!()
}
