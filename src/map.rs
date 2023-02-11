use super::{AnyCollectionRef, Equivalent, KeyContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::iter::Map;
use std::collections::{self, btree_map, hash_map};

mod map_ref;
pub use self::map_ref::MapCollectionRef;

mod map_mut;
pub use self::map_mut::MapCollectionMut;

pub trait MapContainer<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E> + MapCollectionRef<E> + MapCollectionMut<E>,
    E: ?Sized,
{
    type IntoKeys: Iterator<Item = Self::Key>;
    type IntoValues: Iterator<Item = Self::Value>;
    type IntoIter: Iterator<Item = (Self::Key, Self::Value)>;

    fn into_cont_keys(self) -> Self::IntoKeys;
    fn into_cont_values(self) -> Self::IntoValues;
    fn into_cont_iter(self) -> Self::IntoIter;
}

impl<K, V, Q, S> MapContainer<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoKeys = hash_map::IntoKeys<K, V>;
    type IntoValues = hash_map::IntoValues<K, V>;
    type IntoIter = hash_map::IntoIter<K, V>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q, S> MapContainer<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type IntoKeys = hashbrown::hash_map::IntoKeys<K, V>;
    type IntoValues = hashbrown::hash_map::IntoValues<K, V>;
    type IntoIter = hashbrown::hash_map::IntoIter<K, V>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K: Clone, V: Clone, Q, S> MapContainer<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoKeys = Map<im::hashmap::ConsumingIter<(K, V)>, fn((K, V)) -> K>;
    type IntoValues = Map<im::hashmap::ConsumingIter<(K, V)>, fn((K, V)) -> V>;
    type IntoIter = im::hashmap::ConsumingIter<(K, V)>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        #[inline(always)]
        fn key<K1, V1>((key, _): (K1, V1)) -> K1 {
            key
        }
        IntoIterator::into_iter(self).map(key as fn((K, V)) -> K)
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        #[inline(always)]
        fn value<K1, V1>((_, value): (K1, V1)) -> V1 {
            value
        }
        IntoIterator::into_iter(self).map(value as fn((K, V)) -> V)
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q, S> MapContainer<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type IntoKeys = indexmap::map::IntoKeys<K, V>;
    type IntoValues = indexmap::map::IntoValues<K, V>;
    type IntoIter = indexmap::map::IntoIter<K, V>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q> MapContainer<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoKeys = btree_map::IntoKeys<K, V>;
    type IntoValues = btree_map::IntoValues<K, V>;
    type IntoIter = btree_map::IntoIter<K, V>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K: Clone, V: Clone, Q> MapContainer<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoKeys = Map<im::ordmap::ConsumingIter<(K, V)>, fn((K, V)) -> K>;
    type IntoValues = Map<im::ordmap::ConsumingIter<(K, V)>, fn((K, V)) -> V>;
    type IntoIter = im::ordmap::ConsumingIter<(K, V)>;

    #[inline]
    fn into_cont_keys(self) -> Self::IntoKeys {
        #[inline(always)]
        fn key<K1, V1>((key, _): (K1, V1)) -> K1 {
            key
        }
        IntoIterator::into_iter(self).map(key as fn((K, V)) -> K)
    }

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        #[inline(always)]
        fn value<K1, V1>((_, value): (K1, V1)) -> V1 {
            value
        }
        IntoIterator::into_iter(self).map(value as fn((K, V)) -> V)
    }

    #[inline]
    fn into_cont_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}
