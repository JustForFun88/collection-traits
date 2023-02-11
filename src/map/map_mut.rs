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
///
/// # Notes about the implementation of the trait within this crate
///
/// When implementing this trait, you need to be careful about the type `E`
/// of the  lookup key. For greater flexibility, there are no restrictions
/// on the type of search key, but one of two conditions must be met:
///
/// 1. If it is possible to implement it, then it is desirable to specify
///    the condition `E: Equivalent<Self::Key>`.
/// 2. If the first condition cannot be met (e.g. for [`std::collections::HashMap`]),
///    the key **must be** any borrowed form of the container's key type (i.e.
///    `Self::Key: Borrow<E>` ) .
///
/// Note that a container that implements `E: Equivalent<Self::Key>` will also
/// accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but the reverse
/// is not true.
pub trait MapCollectionMut<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E> + MapCollectionRef<E>,
    E: ?Sized,
{
    /// An iterator over the entries of a ` MapContainer` in arbitrary order.
    /// The iterator element type is `&'a mut Self::Value`.
    ///
    /// This `type` is created by the [`MapContainerMut::cont_values_mut()`].
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
    /// // Unfortunately, when calling MapContainerMut methods directly,
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

    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value>;
    fn collection_insert(&mut self, key: Self::Key, value: Self::Value) -> Option<Self::Value>;
    fn collection_remove(&mut self, key: &E) -> Option<Self::Value>;
    fn collection_remove_entry(&mut self, key: &E) -> Option<(Self::Key, Self::Value)>;
    fn collection_clear(&mut self);
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
    /// // You do not need to specify the type E when using MapContainerMut
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
    /// // The `Values` iterator produces values in arbitrary order, so the
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
