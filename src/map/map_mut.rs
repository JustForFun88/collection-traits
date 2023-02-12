use super::{AnyCollectionRef, Equivalent, KeyContain, MapCollectionRef};
use crate::ImOrdMapValueMut;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::iter::Map;
use std::collections::{self, btree_map, hash_map};

/// A trait that allows you to abstract from various types of map collections
/// (associative arrays).
///
/// Provides an API that allows you to add and remove elements, and perform
/// other operations on a table.
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
pub trait MapCollectionMut<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E> + MapCollectionRef<E>,
    E: ?Sized,
{
    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut Self::Value`.
    ///
    /// This `type` is created by the [`MapCollectionMut::collection_values_mut()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionMut;
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<_, _> = [(1, "One".to_owned()), (2, "Two".into())].into();
    ///
    /// // Unfortunately, when calling MapCollectionMut methods directly,
    /// // you need to specify the type E
    /// let mut values = MapCollectionMut::<i32>::collection_values_mut(&mut map);
    /// values.next().map(|v| v.push_str(" Mississippi"));
    /// values.next().map(|v| v.push_str(" Mississippi"));
    ///
    /// // It is fused iterator
    /// assert_eq!(values.next(), None);
    /// assert_eq!(values.next(), None);
    ///
    /// assert_eq!(map.get(&1).unwrap(), &"One Mississippi".to_owned());
    /// assert_eq!(map.get(&2).unwrap(), &"Two Mississippi".to_owned());
    /// ```
    type ValuesMut<'a>: Iterator<Item = &'a mut Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// Returns a mutable reference to the value corresponding to the key.
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
    /// key type (ie `Self::Key: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Key>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Key>` will
    /// also accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::key` collection may need to
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
    /// use collection_traits::MapCollectionMut;
    /// use core::borrow::Borrow;
    /// use hashbrown::HashMap;
    ///
    /// let mut map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);
    ///
    /// // You do not need to specify the type E when calling this `MapCollectionMut`
    /// // method directly.
    /// let value = map1.get_value_mut("a").unwrap();
    /// assert_eq!(value, &mut 1);
    /// *value = 10;
    /// assert_eq!(map1.get_value_mut("a"), Some(&mut 10));
    ///
    /// // Also, there is no need to specify the type E when using MapCollectionMut
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get_value_mut<'a, T>(cont: &'a mut T, key: &T::Key) -> Option<&'a mut T::Value>
    /// where
    ///     T: MapCollectionMut + ?Sized,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// fn get_value_mut_borrow_key<'a, T, Q>(cont: &'a mut T, key: &Q) -> Option<&'a mut T::Value>
    /// where
    ///     Q: ?Sized,
    ///     T: MapCollectionMut<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// assert_eq!(get_value_mut(&mut map1, &"a".to_string()), Some(&mut 10));
    /// // assert_eq!(get_value_mut(&mut map1, "a"), Some(&mut 10)); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(
    ///     get_value_mut_borrow_key(&mut map1, &"a".to_string()),
    ///     Some(&mut 10)
    /// );
    /// assert_eq!(get_value_mut_borrow_key(&mut map1, "a"), Some(&mut 10));
    /// ```
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value>;

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, [`None`] is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionMut;
    /// use std::collections::BTreeMap;
    /// use hashbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    /// // Unfortunately, when calling MapCollectionMut methods directly,
    /// // you need to specify the type E
    /// assert_eq!(
    ///     MapCollectionMut::<i32>::collection_insert(&mut map, 37, "a"),
    ///     None
    /// );
    /// assert_eq!(map.is_empty(), false);
    ///
    /// // But you do not need to specify the type E when using MapCollectionMut
    /// // as trait bound
    /// fn insert<T>(collection: &mut T, k: T::Key, v: T::Value) -> Option<T::Value>
    /// where
    ///     T: MapCollectionMut,
    /// {
    ///     collection.collection_insert(k, v)
    /// }
    ///
    /// assert_eq!(insert(&mut map, 37, "b"), Some("a"));
    ///
    /// let mut map = BTreeMap::new();
    ///
    /// assert_eq!(insert(&mut map, 37, "a"), None);
    /// assert_eq!(insert(&mut map, 37, "b"), Some("a"));
    /// ```
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value>;

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
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
    /// key type (ie `Self::Key: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Key>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Key>` will
    /// also accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::key` collection may need to
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
    /// use collection_traits::MapCollectionMut;
    /// use core::borrow::Borrow;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let mut map = HashMap::new();
    ///
    /// map.insert("a".to_owned(), 1);
    /// assert!(!map.is_empty());
    /// // You do not need to specify the type E when calling this `MapCollectionMut`
    /// // method directly.
    /// assert_eq!(map.collection_remove("a"), Some(1));
    /// assert!(map.is_empty());
    ///
    /// // Also, there is no need to specify the type E when using MapCollectionMut
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn remove<T>(collection: &mut T, k: &T::Key) -> Option<T::Value>
    /// where
    ///     T: MapCollectionMut,
    /// {
    ///     collection.collection_remove(k)
    /// }
    ///
    /// fn remove_borrow_key<T, Q: ?Sized>(collection: &mut T, k: &Q) -> Option<T::Value>
    /// where
    ///     T: MapCollectionMut<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     collection.collection_remove(k)
    /// }
    ///
    /// let mut map = HashMap::from([("a".to_owned(), 1), ("b".into(), 2), ("c".into(), 3)]);
    /// assert_eq!(remove(&mut map, &"a".to_owned()), Some(1));
    /// // assert_eq!(remove(&mut map, "b"), Some(2)); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(remove_borrow_key(&mut map, &"b".to_owned()), Some(2));
    /// assert_eq!(remove_borrow_key(&mut map, "c"), Some(3));
    /// assert!(map.is_empty());
    ///
    /// let mut map = BTreeMap::from([("a".to_owned(), 1), ("b".into(), 2), ("c".into(), 3)]);
    ///
    /// assert_eq!(remove(&mut map, &"a".to_owned()), Some(1));
    /// assert_eq!(remove_borrow_key(&mut map, &"b".to_owned()), Some(2));
    /// assert_eq!(remove_borrow_key(&mut map, "c"), Some(3));
    /// assert!(map.is_empty());
    /// ```
    fn collection_remove(&mut self, key: &E) -> Option<Self::Value>;

    /// Removes a key from the map, returning the stored key and value if the
    /// key was previously in the map.
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
    /// key type (ie `Self::Key: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Key>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Key>` will
    /// also accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::key` collection may need to
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
    /// use collection_traits::MapCollectionMut;
    /// use core::borrow::Borrow;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let mut map = HashMap::new();
    ///
    /// map.insert("a".to_owned(), 1);
    /// assert!(!map.is_empty());
    /// // You do not need to specify the type E when calling this `MapCollectionMut`
    /// // method directly.
    /// assert_eq!(map.collection_remove_entry("a"), Some(("a".to_owned(), 1)));
    /// assert!(map.is_empty());
    ///
    /// // Also, there is no need to specify the type E when using MapCollectionMut
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn remove<T>(collection: &mut T, k: &T::Key) -> Option<(T::Key, T::Value)>
    /// where
    ///     T: MapCollectionMut,
    /// {
    ///     collection.collection_remove_entry(k)
    /// }
    ///
    /// fn remove_borrow_key<T, Q: ?Sized>(collection: &mut T, k: &Q) -> Option<(T::Key, T::Value)>
    /// where
    ///     T: MapCollectionMut<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     collection.collection_remove_entry(k)
    /// }
    ///
    /// let mut map = HashMap::from([("a".to_owned(), 1), ("b".into(), 2), ("c".into(), 3)]);
    /// assert_eq!(remove(&mut map, &"a".to_owned()), Some(("a".to_owned(), 1)));
    /// // Err: expected struct `String`, found `str`
    /// // assert_eq!(remove(&mut map, "b"), Some(("b".to_owned(), 2)));
    ///
    /// assert_eq!(
    ///     remove_borrow_key(&mut map, &"b".to_owned()),
    ///     Some(("b".into(), 2))
    /// );
    /// assert_eq!(remove_borrow_key(&mut map, "c"), Some(("c".into(), 3)));
    /// assert!(map.is_empty());
    ///
    /// let mut map = BTreeMap::from([("a".to_owned(), 1), ("b".into(), 2), ("c".into(), 3)]);
    ///
    /// assert_eq!(remove(&mut map, &"a".to_owned()), Some(("a".into(), 1)));
    /// assert_eq!(
    ///     remove_borrow_key(&mut map, &"b".to_owned()),
    ///     Some(("b".into(), 2))
    /// );
    /// assert_eq!(remove_borrow_key(&mut map, "c"), Some(("c".into(), 3)));
    /// assert!(map.is_empty());
    /// ```
    fn collection_remove_entry(&mut self, key: &E) -> Option<(Self::Key, Self::Value)>;

    /// Clears the map, removing all key-value pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionMut;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let mut map = HashMap::new();
    ///
    /// map.insert("a".to_owned(), 1);
    /// assert!(!map.is_empty());
    /// // Unfortunately, when calling MapCollectionMut methods directly,
    /// // you need to specify the type E
    /// MapCollectionMut::<str>::collection_clear(&mut map);
    /// assert!(map.is_empty());
    ///
    /// // But you do not need to specify the type E when using MapCollectionMut
    /// // as trait bound.
    /// fn clear<T: MapCollectionMut>(collection: &mut T) {
    ///     collection.collection_clear();
    /// }
    ///
    /// let mut map = HashMap::from([("a".to_owned(), 1), ("b".into(), 2)]);
    /// clear(&mut map);
    /// assert!(map.is_empty());
    ///
    /// let mut map = BTreeMap::from([("a".to_owned(), 1), ("b".into(), 2)]);
    /// clear(&mut map);
    /// assert!(map.is_empty());
    /// ```
    fn collection_clear(&mut self);

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(Self::Key, Self::Value)` such
    /// that `f(&Self::Key, &mut Self::Value)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionMut;
    /// use hashbrown::HashMap;
    /// use std::collections::BTreeMap;
    ///
    /// let mut map: HashMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
    /// assert_eq!(map.len(), 8);
    ///
    /// // Unfortunately, when calling MapCollectionMut methods directly,
    /// // you need to specify the type E
    /// MapCollectionMut::<i32>::collection_retain(&mut map, |&k, _| k % 2 == 0);
    ///
    /// // We can see, that the number of elements inside map is changed.
    /// assert_eq!(map.len(), 4);
    ///
    /// let mut vec: Vec<(i32, i32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 0), (2, 20), (4, 40), (6, 60)]);
    ///
    /// // But you do not need to specify the type E when using MapCollectionMut
    /// // as trait bound.
    /// fn retain<T: MapCollectionMut, F>(collection: &mut T, f: F)
    /// where
    ///     F: FnMut(&T::Key, &mut T::Value) -> bool,
    /// {
    ///     collection.collection_retain(f);
    /// }
    ///
    /// let mut map: HashMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
    /// retain(&mut map, |&k, _| k % 2 == 0);
    ///
    /// let mut vec: Vec<(i32, i32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 0), (2, 20), (4, 40), (6, 60)]);
    ///
    /// let mut map: BTreeMap<i32, i32> = (0..8).map(|x| (x, x * 10)).collect();
    /// retain(&mut map, |&k, _| k % 2 == 0);
    ///
    /// let mut vec: Vec<(i32, i32)> = map.iter().map(|(&k, &v)| (k, v)).collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [(0, 0), (2, 20), (4, 40), (6, 60)]);
    /// ```
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool;

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut Self::Value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::MapCollectionMut;
    /// use hashbrown::HashMap;
    ///
    /// let mut map = HashMap::new();
    ///
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // You do not need to specify the type E when using MapCollectionMut
    /// // as trait bound
    /// fn get_mut<T: MapCollectionMut>(container: &mut T) -> Vec<&mut T::Value> {
    ///     container.collection_values_mut().collect::<Vec<_>>()
    /// }
    /// for val in get_mut(&mut map) {
    ///     *val = *val + 10;
    /// }
    ///
    /// assert_eq!(map.len(), 3);
    /// let mut vec: Vec<i32> = Vec::new();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    ///     vec.push(*val);
    /// }
    ///
    /// // The `ValuesMut` iterator produces values in arbitrary order, so the
    /// // values must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [11, 12, 13]);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_>;
}

impl<T, E: ?Sized> MapCollectionMut<E> for &mut T
where
    T: MapCollectionMut<E>,
{
    type ValuesMut<'a> = T::ValuesMut<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        <T as MapCollectionMut<E>>::collection_insert(self, key, value)
    }

    #[inline]
    fn collection_remove(&mut self, key: &E) -> Option<Self::Value> {
        <T as MapCollectionMut<E>>::collection_remove(self, key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &E) -> Option<(Self::Key, Self::Value)> {
        <T as MapCollectionMut<E>>::collection_remove_entry(self, key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        <T as MapCollectionMut<E>>::collection_retain(self, f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        <T as MapCollectionMut<E>>::collection_clear(self)
    }

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        <T as MapCollectionMut<E>>::get_value_mut(self, key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        <T as MapCollectionMut<E>>::collection_values_mut(self)
    }
}

impl<K, V, Q, S> MapCollectionMut<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type ValuesMut<'a> = hash_map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        self.insert(key, value)
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_entry(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q, S> MapCollectionMut<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type ValuesMut<'a> = hashbrown::hash_map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        self.insert(key, value)
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_entry(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q, S> MapCollectionMut<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Clone + Borrow<Q>,
    V: Clone,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type ValuesMut<'a> = Map<im::hashmap::IterMut<'a, K, V>, fn((&'a K, &'a mut V)) -> &'a mut V>
    where
        Self: 'a,
        Self::Key: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        if let Some(old_value) = self.get_mut(key.borrow()) {
            Some(core::mem::replace(old_value, value))
        } else {
            self.insert(key, value)
        }
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_with_key(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        let keys = im::HashMap::keys(self).cloned().collect::<Vec<_>>();
        for key in keys {
            if let Some(value) = self.get_mut(key.borrow()) {
                if !f(&key, value) {
                    self.remove(key.borrow());
                }
            }
        }
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut<'a>(&'a mut self) -> Self::ValuesMut<'a> {
        #[inline(always)]
        fn value_mut<'a, K1, V1>((_, value): (&'a K1, &'a mut V1)) -> &'a mut V1 {
            value
        }
        self.iter_mut()
            .map(value_mut as fn((&'a K, &'a mut V)) -> &'a mut V)
    }
}

impl<K, V, Q, S> MapCollectionMut<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type ValuesMut<'a> = indexmap::map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        self.insert(key, value)
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_entry(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q> MapCollectionMut<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type ValuesMut<'a> = btree_map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        self.insert(key, value)
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_entry(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        self.retain(f)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K: Clone, V: Clone, Q> MapCollectionMut<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type ValuesMut<'a> = ImOrdMapValueMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value> {
        if let Some(old_value) = self.get_mut(key.borrow()) {
            Some(core::mem::replace(old_value, value))
        } else {
            self.insert(key, value)
        }
    }

    #[inline]
    fn collection_remove(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn collection_remove_entry(&mut self, key: &Q) -> Option<(Self::Key, Self::Value)> {
        self.remove_with_key(key)
    }

    #[inline]
    fn collection_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Key, &mut Self::Value) -> bool,
    {
        let keys = im::OrdMap::keys(self).cloned().collect::<Vec<_>>();
        for key in keys {
            if let Some(value) = self.get_mut(key.borrow()) {
                if !f(&key, value) {
                    self.remove(key.borrow());
                }
            }
        }
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        ImOrdMapValueMut::new(self)
    }
}
