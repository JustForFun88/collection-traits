use super::{AnyCollectionRef, Equivalent, KeyContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections::{self, btree_map, hash_map};

/// A private module that guarantees that the user of the [`MapContainerRef`]
/// trait (and other map traits) cannot implement this trait on a container
/// that is not actually an associative array and thus blocks the possibility
/// of violating the invariant provided by the `MapContainerRef` trait, namely
/// the invariant that each possible key appears at most once in the collection.
///
/// SHOULD BE IMPLEMENTED ONLY FOR TYPES THAT REPRESENT SOME TYPE OF ASSOCIATED
/// ARRAY!!!
///
/// Without this private module, the user can implement the `MapContainerRef`
/// trait for example for `[T; N]` where `T: MapContainerRef`.
///
/// [`MapContainerRef`]: crate::MapContainerRef
mod private_map_collections {
    use std::collections;
    pub trait Sealed {}

    impl<K, V, S> Sealed for collections::HashMap<K, V, S> {}

    impl<K, V, S> Sealed for hashbrown::HashMap<K, V, S> {}

    impl<K, V, S> Sealed for im::HashMap<K, V, S> {}

    impl<K, V, S> Sealed for indexmap::IndexMap<K, V, S> {}

    impl<K, V> Sealed for collections::BTreeMap<K, V> {}

    impl<K, V> Sealed for im::OrdMap<K, V> {}

    impl<T: Sealed> Sealed for &T {}

    impl<T: Sealed> Sealed for &mut T {}
}

/// A trait that allows you to abstract from various types of map collections
/// (associative arrays).
///
/// Provides an API that allows you to work with both the owning or
/// reference variable.
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
/// this trait outside of this crate is prohibited.
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
pub trait MapCollectionRef<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E> + Sized + private_map_collections::Sealed,
    E: ?Sized,
{
    /// An iterator over the entries of a ` MapContainer` in arbitrary order.
    /// The iterator element type is `(&'a Self::Key, &'a Self::Value)`.
    ///
    /// This `type` is created by the [`MapCollectionRef::iter_collection()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionRef;
    /// use hashbrown::HashMap;
    ///
    /// let map: HashMap<_, _> = [(1, "a"), (2, "b"), (3, "c")].into();
    ///
    /// // Unfortunately, when calling the `MapCollectionRef` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// let mut iter = MapCollectionRef::<i32>::iter_collection(&map);
    /// let mut vec = vec![iter.next(), iter.next(), iter.next()];
    ///
    /// // The `Iter` iterator produces items in arbitrary order, so the
    /// // items must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [Some((&1, &"a")), Some((&2, &"b")), Some((&3, &"c"))]);
    ///
    /// // It is fused iterator
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next(), None);
    /// ```
    type Iter<'a>: Iterator<Item = (&'a Self::Key, &'a Self::Value)>
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;

    /// Returns the key-value pair corresponding to the supplied key.
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
    /// The lookup key `E` must be either a borrowed form of the container's
    /// key type (i.e. `Self::Key: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Key>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Key>` will
    /// also accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::Key` collection may need to
    /// implement the [`Hash`] and [`Eq`] or [`Ord`] traits. Thus, the corresponding
    /// search key `E` must also implement the corresponding traits.
    ///
    /// If the required traits are [`Hash`] and [`Eq`] then `Hash` and `Eq` on the
    /// lookup key must match those for the key type.
    ///
    /// If the required trait is [`Ord`] than the ordering on the lookup key must
    /// match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionRef;
    /// use hashbrown::HashMap;
    /// use core::borrow::Borrow;
    ///
    /// // There is no need to specify the type `E` when using MapCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get<'a, T>(cont: &'a T, key: &T::Key) -> Option<(&'a T::Key, &'a T::Value)>
    /// where
    ///     T: MapCollectionRef + ?Sized,
    /// {
    ///     cont.get_key_value(key)
    /// }
    ///
    /// fn get_borrow_key<'a, T, Q: ?Sized>(cont: &'a T, key: &Q) -> Option<(&'a T::Key, &'a T::Value)>
    /// where
    ///     T: MapCollectionRef<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     cont.get_key_value(key)
    /// }
    ///
    /// let mut map = HashMap::new();
    /// map.insert("a".to_owned(), 1);
    ///
    /// assert_eq!(get(&map, &"a".to_owned()), Some((&"a".into(), &1)));
    /// // assert_eq!(get(&map, "a"), Some((&"a".into(), &1))); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(get_borrow_key(&map, &"a".to_owned()), Some((&"a".into(), &1)));
    /// assert_eq!(get_borrow_key(&map, "a"), Some((&"a".into(), &1)));
    ///
    /// assert_eq!(get_borrow_key(&map, "b"), None);
    /// ```
    fn get_key_value(&self, key: &E) -> Option<(&Self::Key, &Self::Value)>;

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a Self::Key, &'a Self::Value)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionRef;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);
    ///
    /// // Unfortunately, when calling MapCollectionRef methods directly,
    /// // you need to specify the type E
    /// let mut values = MapCollectionRef::<i32>::iter_collection(&map1).collect::<Vec<_>>();
    /// values.sort_unstable();
    /// assert_eq!(values, [(&1, &10), (&2, &20), (&3, &30)]);
    ///
    /// let map2: BTreeMap<i32, i32> = BTreeMap::from([(4, 40), (5, 50), (6, 60)]);
    ///
    /// // But you do not need to specify the type E when using MapCollectionRef
    /// // as trait bound
    /// fn get_all<T: MapCollectionRef>(container: &T) -> Vec<(&T::Key, &T::Value)> {
    ///     container.iter_collection().collect::<Vec<_>>()
    /// }
    ///
    /// let mut values = get_all(&map1);
    /// values.sort_unstable();
    /// assert_eq!(values, [(&1, &10), (&2, &20), (&3, &30)]);
    ///
    /// let mut values = get_all(&map2);
    /// values.sort_unstable();
    /// assert_eq!(values, [(&4, &40), (&5, &50), (&6, &60)]);
    /// ```
    fn iter_collection(&self) -> Self::Iter<'_>;
}

impl<T, E: ?Sized> MapCollectionRef<E> for &T
where
    T: MapCollectionRef<E>,
{
    type Iter<'a> = T::Iter<'a>
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;
    #[inline]
    fn get_key_value(&self, key: &E) -> Option<(&Self::Key, &Self::Value)> {
        <T as MapCollectionRef<E>>::get_key_value(self, key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        <T as MapCollectionRef<E>>::iter_collection(self)
    }
}

impl<T, E: ?Sized> MapCollectionRef<E> for &mut T
where
    T: MapCollectionRef<E>,
{
    type Iter<'a> = T::Iter<'a>
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;
    #[inline]
    fn get_key_value(&self, key: &E) -> Option<(&Self::Key, &Self::Value)> {
        <T as MapCollectionRef<E>>::get_key_value(self, key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        <T as MapCollectionRef<E>>::iter_collection(self)
    }
}

impl<K, V, Q, S> MapCollectionRef<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Iter<'a> = hash_map::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K, V, Q, S> MapCollectionRef<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type Iter<'a> = hashbrown::hash_map::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K, V, Q, S> MapCollectionRef<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Iter<'a> = im::hashmap::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K, V, Q, S> MapCollectionRef<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type Iter<'a> = indexmap::map::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K, V, Q> MapCollectionRef<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Iter<'a> = btree_map::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<K, V, Q> MapCollectionRef<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Iter<'a> = im::ordmap::Iter<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    #[inline]
    fn get_key_value(&self, key: &Q) -> Option<(&Self::Key, &Self::Value)> {
        self.get_key_value(key)
    }
    #[inline]
    fn iter_collection(&self) -> Self::Iter<'_> {
        self.iter()
    }
}
