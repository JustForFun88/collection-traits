#[cfg(test)]
mod tests;

use super::{AnyCollectionRef, Equivalent, ImOrdMapValueMut, KeyContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::iter::{FlatMap, Map};
use core::slice;
use smallvec::SmallVec;
use std::collections::{self, btree_map, hash_map, linked_list, vec_deque};

/// A trait that allows you to abstract from various types of collections /
/// containers that can have some key and value stored inside.
///
/// Provides a basic API that allows you to change the values of a collection.
///
/// # Note
///
/// This trait does not guarantee:
///
/// 1. Does not guarantee that the key and value are not the same value.
///
/// 2. Does not guarantee that the key and / or value is unique and does
/// not repeat inside the container.
///
/// 3. Does not guarantee that this is a single container `T` or an array
/// of containers `[T; N]` where `T: BaseContainerMut`.
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
pub trait BaseCollectionMut<E = <Self as KeyContain>::Key>
where
    Self: AnyCollectionRef<E>,
    E: ?Sized,
{
    /// The type of the iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a mut Self::Value`.
    ///
    /// It is created by the [`BaseCollectionMut::collection_values_mut()`].
    /// See its documentation for more.
    type ValuesMut<'a>: Iterator<Item = &'a mut Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Note
    ///
    /// Note that the key and value can be the same value (for example,
    /// if the container is a Vec<_>)! In addition, this trait does not
    /// guarantee that the returned value is unique and does not repeat
    /// within the container.
    ///
    /// The lookup key `E` must be either a borrowed form of the container's
    /// key type (ie `Self::Key: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Key>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Key>` will
    /// also accept all `E` lookup keys such as `Self::Key: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, BaseCollectionMut, TryCollectArray};
    /// use core::borrow::Borrow;
    /// use hashbrown::HashMap;
    ///
    /// let mut map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);
    ///
    /// // You do not need to specify the type E when calling this `BaseCollectionMut`
    /// // method directly.
    /// let value = map1.get_value_mut("a").unwrap();
    /// assert_eq!(value, &mut 1);
    /// *value = 10;
    /// assert_eq!(map1.get_value_mut("a"), Some(&mut 10));
    ///
    /// // Also, there is no need to specify the type E when using BaseCollectionMut
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get_value_mut<'a, T>(cont: &'a mut T, key: &T::Key) -> Option<&'a mut T::Value>
    /// where
    ///     T: BaseCollectionMut + ?Sized,
    /// {
    ///     cont.get_value_mut(key)
    /// }
    ///
    /// fn get_value_mut_borrow_key<'a, T, Q>(cont: &'a mut T, key: &Q) -> Option<&'a mut T::Value>
    /// where
    ///     Q: ?Sized,
    ///     T: BaseCollectionMut<Q> + ?Sized,
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
    ///
    /// let iter = (0..3).map(|i| ((i * 3)..((i + 1) * 3)));
    /// let mut arr = iter
    ///     .clone()
    ///     .try_collect_collections_array::<[Vec<_>; 3]>()
    ///     .unwrap();
    ///
    /// for (vec, key_iter) in arr.iter_mut().zip(iter.clone()) {
    ///     for key in key_iter {
    ///         let value = get_value_mut_borrow_key(vec, &key).unwrap();
    ///         *value += 10;
    ///     }
    /// }
    ///
    /// let values = AnyCollectionRef::<i32>::collection_values(&arr)
    ///     .cloned()
    ///     .collect::<Vec<_>>();
    /// assert_eq!(values, vec![10, 11, 12, 13, 14, 15, 16, 17, 18]);
    /// ```
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value>;

    /// Returns an iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a mut Self::Value`.
    ///
    /// # Note
    ///
    /// 1. Note that the key and value can be the same value (for example,
    /// if the container is a Vec<_>)!
    ///
    /// 2. The implementation of the iterator depends on the container type,
    /// so iteration over the keys can take as `O(capacity)` so as `O(len)`
    /// time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, BaseCollectionMut, TryCollectArray};
    /// use hashbrown::HashMap;
    ///
    /// let mut map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);
    ///
    /// // Unfortunately, when calling BaseCollectionMut methods directly,
    /// // you need to specify the type E
    /// let mut values = BaseCollectionMut::<i32>::collection_values_mut(&mut map1)
    ///     .map(|x| x)
    ///     .collect::<Vec<_>>();
    /// values.sort_unstable();
    /// assert_eq!(values, [&10, &20, &30]);
    ///
    /// // But you do not need to specify the type E when using BaseCollectionMut
    /// // as trait bound
    /// fn get_all_values_mut<T: BaseCollectionMut>(container: &mut T) -> Vec<&mut T::Value> {
    ///     container.collection_values_mut().collect::<Vec<_>>()
    /// }
    ///
    /// let mut values = get_all_values_mut(&mut map1);
    /// values.sort_unstable();
    /// assert_eq!(values, [&mut 10, &mut 20, &mut 30]);
    ///
    /// for value in values {
    ///     *value += 100
    /// }
    ///
    /// let mut values = get_all_values_mut(&mut map1);
    /// values.sort_unstable();
    /// assert_eq!(values, [&mut 110, &mut 120, &mut 130]);
    ///
    /// let mut arr = (0..2)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)))
    ///     .try_collect_collections_array::<[Vec<_>; 2]>()
    ///     .unwrap();
    ///
    /// let values = get_all_values_mut(&mut arr);
    ///
    /// for value in values {
    ///     *value += 100
    /// }
    ///
    /// let mut values = AnyCollectionRef::<i32>::collection_values(&arr).collect::<Vec<_>>();
    /// values.sort();
    /// assert_eq!(values, [&100, &101, &102, &103, &104, &105]);
    /// ```
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_>;
}

impl<T, E: ?Sized> BaseCollectionMut<E> for &mut T
where
    T: ?Sized + BaseCollectionMut<E>,
{
    type ValuesMut<'a> = T::ValuesMut<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        <T as BaseCollectionMut<E>>::get_value_mut(self, key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        <T as BaseCollectionMut<E>>::collection_values_mut(self)
    }
}

macro_rules! impl_base_container_mut_for_vec_type {
    (impl for $type_n:ty, T $(: $bound:ident)?, IterMut = $iter_mut:ty) => (
        impl<T, E> BaseCollectionMut<E> for $type_n
        where
            $(T: $bound,)?
            E: ?Sized + Equivalent<T>,
        {
            type ValuesMut<'a> = $iter_mut
            where
                Self: 'a,
                Self::Value: 'a;

            #[inline]
            fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
                self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
            }

            #[inline]
            fn collection_values_mut<'a>(&'a mut self) -> Self::ValuesMut<'a> {
                self.iter_mut()
            }
        }
    );
}

impl_base_container_mut_for_vec_type! {
    impl for [T], T, IterMut = core::slice::IterMut<'a, T>
}

impl_base_container_mut_for_vec_type! {
    impl for Vec<T>, T, IterMut = core::slice::IterMut<'a, T>
}

impl_base_container_mut_for_vec_type! {
    impl for im::Vector<T>, T: Clone, IterMut = im::vector::IterMut<'a, T>
}

impl_base_container_mut_for_vec_type! {
    impl for collections::VecDeque<T>, T, IterMut = vec_deque::IterMut<'a, T>
}

impl_base_container_mut_for_vec_type! {
    impl for collections::LinkedList<T>, T, IterMut = linked_list::IterMut<'a, T>
}

impl<T, A, E> BaseCollectionMut<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type ValuesMut<'a> = slice::IterMut<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        self.iter_mut().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.iter_mut()
    }
}

impl<K, V, Q, S> BaseCollectionMut<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type ValuesMut<'a>  = hash_map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }
    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q, S> BaseCollectionMut<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type ValuesMut<'a>  = hashbrown::hash_map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }
    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q, S> BaseCollectionMut<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Clone + Borrow<Q>,
    V: Clone,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type ValuesMut<'a> = Map<im::hashmap::IterMut<'a, K, V>, fn((&'a K, &'a mut V)) -> &'a mut V>
    where
        Self: 'a,
        Self::Value: 'a;

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

impl<K, V, Q, S> BaseCollectionMut<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type ValuesMut<'a>  = indexmap::map::ValuesMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }
    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K, V, Q> BaseCollectionMut<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type ValuesMut<'a>  = btree_map::ValuesMut<'a, K, V> where Self:'a, K: 'a, V:'a;

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }
    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        self.values_mut()
    }
}

impl<K: Clone, V: Clone, Q> BaseCollectionMut<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type ValuesMut<'a> = ImOrdMapValueMut<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &Q) -> Option<&mut Self::Value> {
        self.get_mut(key)
    }

    #[inline]
    fn collection_values_mut(&mut self) -> Self::ValuesMut<'_> {
        ImOrdMapValueMut::new(self)
    }
}

impl<E, T, const N: usize> BaseCollectionMut<E> for [T; N]
where
    E: ?Sized,
    T: BaseCollectionMut<E>,
{
    type ValuesMut<'a> = FlatMap<slice::IterMut<'a, T>, T::ValuesMut<'a>, fn(&'a mut T) -> T::ValuesMut<'a>>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn get_value_mut(&mut self, key: &E) -> Option<&mut Self::Value> {
        if let Some(container) = self.iter_mut().find(|x| x.contains_eq(key)) {
            return container.get_value_mut(key);
        }
        None
    }

    #[inline]
    fn collection_values_mut<'a>(&'a mut self) -> Self::ValuesMut<'a> {
        #[inline(always)]
        fn values_mut_iter<E1: ?Sized, T1: BaseCollectionMut<E1>>(
            item: &mut T1,
        ) -> T1::ValuesMut<'_> {
            item.collection_values_mut()
        }
        self.iter_mut()
            .flat_map(values_mut_iter as fn(&'a mut T) -> T::ValuesMut<'a>)
    }
}
