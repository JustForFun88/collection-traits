use super::{AnyCollectionRef, Equivalent, KeyContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::iter::Map;
use std::collections::{self, btree_map, hash_map};

mod map_ref;
pub use self::map_ref::MapCollectionRef;

mod map_mut;
pub use self::map_mut::MapCollectionMut;

/// A trait that allows you to abstract from various types of map
/// collections (associative arrays).
///
/// Provides an API that allows you to convert a `MapCollection`
/// to a consuming iterator.
///
/// # Note
///
/// Note that this trait guarantees that:
///
/// 1. That key and value are not the same.
///
/// 2. That the return value and the key itself are unique and do not
/// repeat within the container.
///
/// To prevent this invariant from being violated, the implementation of
/// this trait outside of this crate is prohibited (via [`MapCollectionRef`]).
//
// # Notes about the implementation of the trait within this crate
//
// When implementing this trait, you need to be careful about the type `E`
// of the  lookup key. For greater flexibility, there are no restrictions
// on the type of search key, but one of two conditions must be met:
//
// 1. If it is possible to implement it, then it is desirable to specify
//    the condition `E: Equivalent<Self::Key>`.
// 2. If the first condition cannot be met (e.g. for [`std::collections::HashMap`]),
//    the key **must be** any borrowed form of the container's key type (i.e.
//    `Self::Key: Borrow<E>` ) .
//
// Note that a container that implements `E: Equivalent<Self::Key>` will also
// accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but the reverse
// is not true.
pub trait MapCollection<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E> + MapCollectionRef<E> + MapCollectionMut<E>,
    E: ?Sized,
{
    /// An owning iterator over the keys of a collection in arbitrary order.
    /// The iterator element type is `Self::Key`.
    ///
    /// This `type` is created by the [`MapCollection::into_collection_keys()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapContainer methods directly,
    /// // you need to specify the type E
    /// let mut keys = MapCollection::<i32>::into_collection_keys(map);
    /// let mut vec = vec![keys.next(), keys.next(), keys.next()];
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [Some(1), Some(2), Some(3)]);
    ///
    /// // It is fused iterator
    /// assert_eq!(keys.next(), None);
    /// assert_eq!(keys.next(), None);
    /// ```
    type IntoKeys: Iterator<Item = Self::Key>;

    /// An owning iterator over the values of a collection in arbitrary order.
    /// The iterator element type is `Self::Value`.
    ///
    /// This `type` is created by the [`MapCollection::into_collection_values()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapContainer methods directly,
    /// // you need to specify the type E
    /// let mut values = MapCollection::<i32>::into_collection_values(map);
    /// let mut vec = vec![values.next(), values.next(), values.next()];
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [Some("a"), Some("b"), Some("c")]);
    ///
    /// // It is fused iterator
    /// assert_eq!(values.next(), None);
    /// assert_eq!(values.next(), None);
    /// ```
    type IntoValues: Iterator<Item = Self::Value>;

    /// An owning iterator over the entries of a collection in arbitrary order.
    /// The iterator element type is `(Self::Key, Self::Value)`.
    ///
    /// This `type` is created by the [`MapCollection::into_collection_iter()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapContainer methods directly,
    /// // you need to specify the type E
    /// let mut iter = MapCollection::<i32>::into_collection_iter(map);
    /// let mut vec = vec![iter.next(), iter.next(), iter.next()];
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [Some((1, "a")), Some((2, "b")), Some((3, "c"))]);
    ///
    /// // It is fused iterator
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None);
    /// ```
    type IntoIter: Iterator<Item = (Self::Key, Self::Value)>;

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type
    /// is `Self::Key`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapCollection methods directly,
    /// // you need to specify the type E
    /// let mut vec = MapCollection::<i32>::into_collection_keys(map).collect::<Vec<_>>();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// // But you do not need to specify the type E when using MapCollection
    /// // as trait bound
    /// fn collection_keys<T>(collection: T) -> impl Iterator<Item = T::Key>
    /// where
    ///     T: MapCollection,
    /// {
    ///     collection.into_collection_keys()
    /// }
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_keys(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    ///
    /// let map: BTreeMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_keys(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    fn into_collection_keys(self) -> Self::IntoKeys;

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type
    /// is `Self::Value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapCollection methods directly,
    /// // you need to specify the type E
    /// let mut vec = MapCollection::<i32>::into_collection_values(map).collect::<Vec<_>>();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    ///
    /// // But you do not need to specify the type E when using MapCollection
    /// // as trait bound
    /// fn collection_values<T>(collection: T) -> impl Iterator<Item = T::Value>
    /// where
    ///     T: MapCollection,
    /// {
    ///     collection.into_collection_values()
    /// }
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_values(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    ///
    /// let map: BTreeMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_values(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    fn into_collection_values(self) -> Self::IntoValues;

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollection;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling MapCollection methods directly,
    /// // you need to specify the type E
    /// let mut vec = MapCollection::<i32>::into_collection_iter(map).collect::<Vec<_>>();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, "a"), (2, "b"), (3, "c")]);
    ///
    /// // But you do not need to specify the type E when using MapCollection
    /// // as trait bound
    /// fn collection_iter<T>(collection: T) -> T::IntoIter
    /// where
    ///     T: MapCollection,
    /// {
    ///     collection.into_collection_iter()
    /// }
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_iter(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, "a"), (2, "b"), (3, "c")]);
    ///
    /// let map: BTreeMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// let mut vec = collection_iter(map).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(1, "a"), (2, "b"), (3, "c")]);
    /// ```
    fn into_collection_iter(self) -> Self::IntoIter;
}

impl<K, V, Q, S> MapCollection<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoKeys = hash_map::IntoKeys<K, V>;
    type IntoValues = hash_map::IntoValues<K, V>;
    type IntoIter = hash_map::IntoIter<K, V>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q, S> MapCollection<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type IntoKeys = hashbrown::hash_map::IntoKeys<K, V>;
    type IntoValues = hashbrown::hash_map::IntoValues<K, V>;
    type IntoIter = hashbrown::hash_map::IntoIter<K, V>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K: Clone, V: Clone, Q, S> MapCollection<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoKeys = Map<im::hashmap::ConsumingIter<(K, V)>, fn((K, V)) -> K>;
    type IntoValues = Map<im::hashmap::ConsumingIter<(K, V)>, fn((K, V)) -> V>;
    type IntoIter = im::hashmap::ConsumingIter<(K, V)>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        #[inline(always)]
        fn key<K1, V1>((key, _): (K1, V1)) -> K1 {
            key
        }
        IntoIterator::into_iter(self).map(key as fn((K, V)) -> K)
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        #[inline(always)]
        fn value<K1, V1>((_, value): (K1, V1)) -> V1 {
            value
        }
        IntoIterator::into_iter(self).map(value as fn((K, V)) -> V)
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q, S> MapCollection<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type IntoKeys = indexmap::map::IntoKeys<K, V>;
    type IntoValues = indexmap::map::IntoValues<K, V>;
    type IntoIter = indexmap::map::IntoIter<K, V>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K, V, Q> MapCollection<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoKeys = btree_map::IntoKeys<K, V>;
    type IntoValues = btree_map::IntoValues<K, V>;
    type IntoIter = btree_map::IntoIter<K, V>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        self.into_keys()
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        self.into_values()
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}

impl<K: Clone, V: Clone, Q> MapCollection<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoKeys = Map<im::ordmap::ConsumingIter<(K, V)>, fn((K, V)) -> K>;
    type IntoValues = Map<im::ordmap::ConsumingIter<(K, V)>, fn((K, V)) -> V>;
    type IntoIter = im::ordmap::ConsumingIter<(K, V)>;

    #[inline]
    fn into_collection_keys(self) -> Self::IntoKeys {
        #[inline(always)]
        fn key<K1, V1>((key, _): (K1, V1)) -> K1 {
            key
        }
        IntoIterator::into_iter(self).map(key as fn((K, V)) -> K)
    }

    #[inline]
    fn into_collection_values(self) -> Self::IntoValues {
        #[inline(always)]
        fn value<K1, V1>((_, value): (K1, V1)) -> V1 {
            value
        }
        IntoIterator::into_iter(self).map(value as fn((K, V)) -> V)
    }

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        IntoIterator::into_iter(self)
    }
}
