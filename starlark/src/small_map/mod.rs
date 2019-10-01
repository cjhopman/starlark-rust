use indexmap::{Equivalent, IndexMap};
use std::cell::RefCell;
use std::hash::{Hash, Hasher};

const THRESHOLD: usize = 12;

#[macro_use]
mod macros;

pub struct BorrowedHash<'a, Q: SmallHash + ?Sized> {
    hash: u32,
    v: &'a Q,
}

impl<'a, Q: SmallHash + ?Sized> BorrowedHash<'a, Q> {
    fn new(v: &'a Q) -> Self {
        BorrowedHash {
            hash: v.get_hash() as u32,
            v,
        }
    }
}

impl<'a, Q, V> Equivalent<Hashed<V>> for BorrowedHash<'a, Q> 
    where V: SmallHash, Q: SmallHash + Equivalent<V> + ?Sized
{
    fn equivalent(&self, key: &Hashed<V>) -> bool {
        self.hash == key.hash && self.v.equivalent(&key.v)
    }
}

impl<'a, Q: SmallHash + ?Sized> Hash for BorrowedHash<'a, Q> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.hash)
    }
}

pub trait SmallHash: Eq {
    fn get_hash(&self) -> u64;
}

impl <T: Hash + Eq + ?Sized> SmallHash for T {
    fn get_hash(&self) -> u64 { 
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()        
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Hashed<V: SmallHash> {
    hash: u32,
    v: V,
}

impl<V: SmallHash> Hash for Hashed<V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u32(self.hash)
    }
}

impl<V: SmallHash> Hashed<V> {
    fn new(v: V) -> Self {
        Hashed {
            hash: v.get_hash() as u32,
            v,
        }
    }

    fn hashed(hash: u32, v: V) -> Self {
        Self{hash, v}
    }

    fn val(&self) -> &V {
        &self.v
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct VecMap<K: SmallHash, V> {
    hashes: [u32; THRESHOLD],
    values: Vec<(K, V)>,
}

pub struct VMKeys<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMKeys<'a, K, V> {
    fn map(tup: &'a (K, V)) -> <Self as Iterator>::Item {
        &tup.0
    }

    fn next_back(&mut self) -> Option<&'a K> {
        self.iter.next_back().map(Self::map)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMKeys<'a, K, V> {
    type Item = &'a K;

    def_iter!(Self::map);
}

pub struct VMValues<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMValues<'a, K, V> {
    fn map(tup: &'a (K, V)) -> <Self as Iterator>::Item {
        &tup.1
    }

    fn next_back(&mut self) -> Option<<Self as Iterator>::Item> {
        self.iter.next_back().map(Self::map)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMValues<'a, K, V> {
    type Item = &'a V;

    def_iter!(Self::map);
}

pub struct VMIter<'a, K: 'a, V: 'a> {
    iter: std::slice::Iter<'a, (K, V)>,
}

impl<'a, K: 'a, V: 'a> VMIter<'a, K, V> {
    fn map(tup: &(K, V)) -> (&K, &V) {
        (&tup.0, &tup.1)
    }

    fn next_back(&mut self) -> Option<<Self as Iterator>::Item> {
        self.iter.next_back().map(Self::map)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    def_iter!(Self::map);
}

pub struct VMIntoIter<K, V> {
    iter: std::vec::IntoIter<(K, V)>,
}

impl<K, V> VMIntoIter<K, V> {
    fn map(tup: (K, V)) -> (K, V) {
        tup
    }

    fn next_back(&mut self) -> Option<<Self as Iterator>::Item> {
        self.iter.next_back().map(Self::map)
    }
}

impl<'a, K: 'a, V: 'a> Iterator for VMIntoIter<K, V> {
    type Item = (K, V);

    def_iter!(Self::map);
}

impl<K: SmallHash, V> VecMap<K, V> {
    fn with_capacity(n: usize) -> Self {
        Self {
            hashes: [0; THRESHOLD],
            values: Vec::with_capacity(n),
        }
    }

    // TODO: use Equivalent
    pub fn get<Q>(&self, key: &Q) -> Option<&V> 
        where Q: ?Sized + SmallHash + Equivalent<K>
    {
        let hash = key.get_hash() as u32;
        for i in 0..self.values.len() {
            if self.hashes[i] == hash {
                let v = &self.values[i];
                if key.equivalent(&v.0) {
                    return Some(&v.1)
                }
            }
        }
        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let hash = key.get_hash() as u32;
        self.get_mut_hashed(hash, key)
    }

    fn get_mut_hashed(&mut self, hash: u32, key: &K) -> Option<&mut V> {
        for i in 0..self.values.len() {
            if self.hashes[i] == hash {
                if self.values[i].0 == *key {
                    return Some(&mut self.values[i].1)
                }
            }
        }
        None
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where Q: SmallHash + Equivalent<K> + ?Sized,
    {
        let hash = key.get_hash() as u32;
        for i in 0..self.values.len() {
            if self.hashes[i] == hash {
                 if key.equivalent(&self.values[i].0) {
                     return true;
                 }
            }
        }
        return false;
    }

    pub fn insert(&mut self, key: K, mut value: V) -> Option<V> {
        let hash = key.get_hash() as u32;
        if let Some(v) = self.get_mut_hashed(hash, &key) {
            std::mem::swap(v, &mut value);
            Some(value)
        } else {
            let i = self.values.len();
            self.hashes[i] = hash;
            self.values.push((key, value));
            None
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
            where Q: ?Sized + SmallHash + Equivalent<K>
    {
        let len = self.values.len();
        if len == 0 {
            return None;
        }

        let hash = key.get_hash() as u32;
        for i in 0..len {
            if self.hashes[i] == hash {
                 if key.equivalent(&self.values[i].0) {
                     for j in i..len - 1 {
                         self.hashes[j] = self.hashes[j + 1];
                     }
                     return Some(self.values.remove(i).1);
                 }
            }
        }
        None
    }

    fn drain_to(&mut self, map: &mut IndexMap<Hashed<K>, V>) {
        let hashes = &self.hashes;
        let values = &mut self.values;

        map.extend(values.drain(..).enumerate().map(|(i, p)| (Hashed::hashed(hashes[i], p.0), p.1)));
    }

    fn len(&self) -> usize {
        self.values.len()
    }

    fn is_empty(&self) -> bool {
        self.values.is_empty()
    }


    pub fn values(&self) -> VMValues<K, V> {
        VMValues {
            iter: self.values.iter(),
        }
    }


    pub fn keys(&self) -> VMKeys<K, V> {
        VMKeys {
            iter: self.values.iter(),
        }
    }

    pub fn into_iter(self) -> VMIntoIter<K, V> {
        VMIntoIter{
            iter: self.values.into_iter()
        }
    }

    pub fn iter(&self) -> VMIter<K, V> {
        VMIter {
            iter: self.values.iter(),
        }
    }
}

impl<K: SmallHash, V> Default for VecMap<K, V> {
    fn default() -> Self {
        Self {
            hashes: [0; THRESHOLD],
            values: Vec::new(),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum MapHolder<K: SmallHash, V> {
    Vec(VecMap<K, V>),
    Map(IndexMap<Hashed<K>, V>),
}

pub enum MHKeys<'a, K: SmallHash + 'a, V: 'a> {
    Vec(VMKeys<'a, K, V>),
    Map(indexmap::map::Keys<'a, Hashed<K>, V>),
}

impl<'a, K: SmallHash + 'a, V: 'a> Iterator for MHKeys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MHKeys::Vec(iter) => iter.next(),
            MHKeys::Map(iter) => iter.next().map(Hashed::val),
        }
    }
}



pub enum MHValues<'a, K: SmallHash + 'a, V: 'a> {
    Vec(VMValues<'a, K, V>),
    Map(indexmap::map::Values<'a, Hashed<K>, V>),
}

impl<'a, K: SmallHash + 'a, V: 'a> Iterator for MHValues<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MHValues::Vec(iter) => iter.next(),
            MHValues::Map(iter) => iter.next(),
        }
    }
}

pub enum MHIter<'a, K: SmallHash + 'a, V: 'a> {
    Vec(VMIter<'a, K, V>),
    Map(indexmap::map::Iter<'a, Hashed<K>, V>),
}

impl<'a, K: SmallHash + 'a, V: 'a> Iterator for MHIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MHIter::Vec(iter) => iter.next(),
            MHIter::Map(iter) => iter.next().map(|(hk, v)| (hk.val(), v)),
        }
    }

    // def_iter!(|e| match e {})
}


pub enum MHIntoIter<K: SmallHash, V> {
    Vec(VMIntoIter<K, V>),
    Map(indexmap::map::IntoIter<Hashed<K>, V>),
}

impl<K: SmallHash, V> Iterator for MHIntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MHIntoIter::Vec(iter) => iter.next(),
            MHIntoIter::Map(iter) => iter.next().map(|(hk, v)| (hk.v, v)),
        }
    }

    // def_iter!(|e| match e {})
}


impl<K: SmallHash, V> MapHolder<K, V> {
    fn with_capacity(n: usize) -> Self {
        if n < THRESHOLD {
            MapHolder::Vec(VecMap::with_capacity(n))
        } else {
            MapHolder::Map(IndexMap::with_capacity(n))
        }
    }
}

impl<K: SmallHash, V> Default for MapHolder<K, V> {
    fn default() -> Self {
        MapHolder::Vec(VecMap::default())
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct SmallMap<K: SmallHash, V> {
    state: MapHolder<K, V>,
}

impl<K: SmallHash, V> Default for SmallMap<K, V> {
    fn default() -> Self {
        Self {
            state: Default::default(),
        }
    }
}

impl<K: SmallHash, V> SmallMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(n: usize) -> Self {
        Self {
            state: MapHolder::with_capacity(n),
        }
    }

    pub fn keys(&self) -> MHKeys<K, V> {
        match self.state {
            MapHolder::Vec(ref v) => MHKeys::Vec(v.keys()),
            MapHolder::Map(ref m) => MHKeys::Map(m.keys()),
        }
    }

    pub fn values(&self) -> MHValues<K, V> {
        match self.state {
            MapHolder::Vec(ref v) => MHValues::Vec(v.values()),
            MapHolder::Map(ref m) => MHValues::Map(m.values()),
        }
    }

    pub fn iter(&self) -> MHIter<K, V> {
        match self.state {
            MapHolder::Vec(ref v) => MHIter::Vec(v.iter()),
            MapHolder::Map(ref m) => MHIter::Map(m.iter()),
        }
    }

    pub fn into_iter(self) -> MHIntoIter<K, V> {
        match self.state {
            MapHolder::Vec(v) => MHIntoIter::Vec(v.into_iter()),
            MapHolder::Map(m) => MHIntoIter::Map(m.into_iter()),
        }
    }

    pub fn get<Q> (&self, key: &Q) -> Option<&V> 
        where Q: SmallHash + Equivalent<K> + ?Sized,
    {
        match self.state {
            MapHolder::Vec(ref v) => v.get(key),
            MapHolder::Map(ref m) => m.get(&BorrowedHash::new(key)),
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        match self.state {
            MapHolder::Vec(ref mut v) => v.get_mut(key),
            MapHolder::Map(ref mut m) => m.get_mut(&BorrowedHash::new(key)),
        }
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where Q: SmallHash + Equivalent<K> + ?Sized,
    {
        match self.state {
            MapHolder::Vec(ref v) => v.contains_key(key),
            MapHolder::Map(ref m) => m.contains_key(&BorrowedHash::new(key)),
        }
    }

    fn upgrade(&mut self) {
        let mut holder = MapHolder::Map(IndexMap::with_capacity(THRESHOLD));
        std::mem::swap(&mut self.state, &mut holder);

        if let MapHolder::Vec(ref mut v) = holder {
            if let MapHolder::Map(ref mut m) = self.state {
                v.drain_to(m);
                return;
            }            
        }

        unreachable!()
    }

    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        match self.state {
            MapHolder::Map(ref mut m) => { return m.insert(Hashed::new(key), val); }
            MapHolder::Vec(ref mut v) => {
                if v.len() + 1 < THRESHOLD {
                    return v.insert(key, val);
                }
            }
        }

        self.upgrade();
        if let MapHolder::Map(ref mut m) = self.state { 
            return m.insert(Hashed::new(key), val);
        }

        unreachable!()
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where Q: ?Sized + SmallHash + Equivalent<K>
    {
        match self.state {
            MapHolder::Vec(ref mut v) => v.remove(key),
            MapHolder::Map(ref mut m) => m.shift_remove(&BorrowedHash::new(key)),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self.state {
            MapHolder::Vec(ref v) => v.is_empty(),
            MapHolder::Map(ref m) => m.is_empty(),
        }
    }


    pub fn len(&self) -> usize {
        match self.state {
            MapHolder::Vec(ref v) => v.len(),
            MapHolder::Map(ref m) => m.len(),
        }
    }

    pub fn clear(&mut self) {
        self.state = MapHolder::default();
    }

    pub fn pop(&mut self) -> Option<(K, V)> {
        unimplemented!()
    }
}

impl<K, V> IntoIterator for SmallMap<K, V>
where
    K: SmallHash,
{
    type Item = (K, V);
    type IntoIter = MHIntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}


impl<'a, K, V> IntoIterator for &'a SmallMap<K, V>
where
    K: SmallHash,
{
    type Item = (&'a K, &'a V);
    type IntoIter = MHIter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut SmallMap<K, V>
where
    K: SmallHash,
{
    type Item = (&'a K, &'a V);
    // TODO: should be MHIterMut
    type IntoIter = MHIter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
