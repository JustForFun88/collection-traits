#[cfg(test)]
mod tests;

use super::{Equivalent, KeyContain, ValueContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use core::iter::FlatMap;
use core::slice;
use smallvec::SmallVec;
use std::collections::{
    self, binary_heap, btree_map, btree_set, hash_map, hash_set, linked_list, vec_deque,
};

/// A trait that allows you to abstract from various types of collections /
/// containers that can have some key and value stored inside.
///
/// Provides a basic API that allows you to work with a variable that owns
/// a collection or array of collections, as well as a variable that references
/// to a collection or array of collections.
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
/// of containers `[T; N]` where `T: AnyCollectionRef`.
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
pub trait AnyCollectionRef<E = <Self as KeyContain>::Key>
where
    Self: KeyContain + ValueContain,
    E: ?Sized,
{
    /// The type of the iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a Self::Key`.
    ///
    /// It is created by the [`AnyCollectionRef::collection_keys()`].
    /// See its documentation for more.
    /// 
    /// # Note
    /// 
    /// This type can be the same type as [`AnyCollectionRef::Values<'a>`].
    type Keys<'a>: Iterator<Item = &'a Self::Key>
    where
        Self: 'a,
        Self::Key: 'a;

    /// The type of the iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a Self::Value`.
    /// 
    /// It is created by the [`AnyCollectionRef::collection_values()`].
    /// See its documentation for more.
    /// 
    /// # Note
    /// 
    /// This type can be the same type as [`AnyCollectionRef::Keys<'a>`]
    type Values<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// Returns the number of elements in the container. More precisely
    /// returns the number of elements `V: Value`.
    ///
    /// # Note
    ///
    /// Note that this may not be the same as the number of elements in the
    /// container. For example, for `a = [T; N]` where `T: AnyCollectionRef`,
    /// `a.len() = N`, but
    /// `a.collection_len() = a.iter().map(|x| x.collection_len()).sum()`.
    ///
    /// You will also have to specify the type `E` when calling this method if
    /// the compiler cannot infer this from the context. This usually happens
    /// when you call the given method directly on the object, rather than
    /// behind a generic inside a function (see examples below).
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    ///
    /// let mut map1: HashMap<String, i32> = HashMap::new();
    ///
    /// // Unfortunately, when calling AnyCollectionRef methods directly,
    /// // you need to specify the type E
    /// assert_eq!(AnyCollectionRef::<String>::collection_len(&map1), 0);
    /// assert_eq!(AnyCollectionRef::<str>::collection_len(&map1), 0);
    ///
    /// map1.insert("a".to_owned(), 1);
    ///
    /// let map2: HashMap<usize, usize> = HashMap::from([(1, 1), (2, 2)]);
    ///
    /// // But you do not need to specify the type E when using AnyCollectionRef
    /// // as trait bound
    /// fn get_len<T: AnyCollectionRef>(container: &T) -> usize {
    ///     container.collection_len()
    /// }
    ///
    /// assert_eq!(get_len(&map1), 1);
    /// assert_eq!(get_len(&map2), 2);
    ///
    /// let arr = (0..3)
    ///     .map(|_| 0..3)
    ///     .try_collect_collections_array::<[Vec<_>; 3]>()
    ///     .unwrap();
    ///
    /// // Array::len and AnyCollectionRef::collection_len are not the same value
    /// assert_eq!(arr.len(), 3);
    /// assert_eq!(get_len(&arr), 9);
    /// ```
    fn collection_len(&self) -> usize;

    /// Returns `true` if the container contains no `V: Value` elements.
    ///
    /// # Note
    ///
    /// Note that this does not mean that the container is actually empty.
    /// For example, for `a = [T; N]` where `T: AnyCollectionRef`, `a.len() = N`,
    /// but `a.is_collection_empty() = <[T; N] as AnyCollectionRef<E>>::collection_len(self) == 0`.
    ///
    /// You will also have to specify the type `E` when calling this method if
    /// the compiler cannot infer this from the context. This usually happens
    /// when you call the given method directly on the object, rather than
    /// behind a generic inside a function (see examples below).
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    ///
    /// let mut map1: HashMap<String, i32> = HashMap::new();
    ///
    /// // Unfortunately, when calling AnyCollectionRef methods directly,
    /// // you need to specify the type E
    /// assert!(AnyCollectionRef::<String>::is_collection_empty(&map1));
    /// assert!(AnyCollectionRef::<str>::is_collection_empty(&map1));
    ///
    /// map1.insert("a".to_owned(), 1);
    ///
    /// let map2: HashMap<usize, usize> = HashMap::from([(1, 1), (2, 2)]);
    ///
    /// // But you do not need to specify the type E when using AnyCollectionRef
    /// // as trait bound
    /// fn is_collection_empty<T: AnyCollectionRef>(container: &T) -> bool {
    ///     container.is_collection_empty()
    /// }
    ///
    /// assert!(!is_collection_empty(&map1));
    /// assert!(!is_collection_empty(&map2));
    ///
    /// let arr = (0..3)
    ///     .map(|_| 0..0)
    ///     .try_collect_collections_array::<[Vec<_>; 3]>()
    ///     .unwrap();
    ///
    /// // Array::len and AnyCollectionRef::collection_len are not the same value
    /// assert!(!arr.is_empty());
    /// assert!(is_collection_empty(&arr));
    /// ```
    fn is_collection_empty(&self) -> bool;

    /// Returns `true` if the container contains a value for the
    /// specified key.
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
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    /// use core::borrow::Borrow;
    ///
    /// let map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);
    ///
    /// // You do not need to specify the type E when calling this `AnyCollectionRef`
    /// // method directly.
    /// assert!(map1.contains_eq(&"a".to_string()));
    /// assert!(map1.contains_eq("b"));
    ///
    /// // Also, there is no need to specify the type E when using AnyCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn contain_key<T>(cont: &T, key: &T::Key) -> bool
    /// where
    ///     T: AnyCollectionRef + ?Sized,
    /// {
    ///     cont.contains_eq(key)
    /// }
    ///
    /// fn contain_borrow_key<T, Q: ?Sized>(cont: &T, key: &Q) -> bool
    /// where
    ///     T: AnyCollectionRef<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     cont.contains_eq(key)
    /// }
    ///
    /// assert!(contain_key(&map1, &"a".to_string()));
    /// // assert!(contain_key(&map1, "a")); // Err: expected struct `String`, found `str`
    ///
    /// assert!(contain_borrow_key(&map1, &"a".to_string()));
    /// assert!(contain_borrow_key(&map1, "a"));
    ///
    /// let arr = (0..3)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
    ///     .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
    ///     .unwrap();
    ///
    /// assert!(contain_key(&arr, &"1".to_string()));
    /// assert!(contain_borrow_key(&arr, &"5".to_string()));
    /// assert!(contain_borrow_key(&arr, "8"));
    /// ```
    fn contains_eq(&self, key: &E) -> bool;

    /// Returns a reference to the value corresponding to the key.
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
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    /// use core::borrow::Borrow;
    ///
    /// let map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);
    ///
    /// // You do not need to specify the type E when calling this `AnyCollectionRef`
    /// // method directly.
    /// assert_eq!(map1.get_value(&"a".to_string()), Some(&1));
    /// assert_eq!(map1.get_value("b"), Some(&2));
    ///
    /// // Also, there is no need to specify the type E when using AnyCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get_value<'a, 'b, T>(cont: &'a T, key: &'b T::Key) -> Option<&'a T::Value>
    /// where
    ///     T: AnyCollectionRef + ?Sized,
    /// {
    ///     cont.get_value(key)
    /// }
    ///
    /// fn get_value_borrow_key<'a, 'b, T, Q: ?Sized>(cont: &'a T, key: &'b Q) -> Option<&'a T::Value>
    /// where
    ///     T: AnyCollectionRef<Q> + ?Sized,
    ///     T::Key: Borrow<Q>,
    /// {
    ///     cont.get_value(key)
    /// }
    ///
    /// assert_eq!(get_value(&map1, &"a".to_string()), Some(&1));
    /// // assert_eq!(get_value(&map1, "a"), Some(&1)); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(get_value_borrow_key(&map1, &"a".to_string()), Some(&1));
    /// assert_eq!(get_value_borrow_key(&map1, "a"), Some(&1));
    ///
    /// let arr = (0..3)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
    ///     .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
    ///     .unwrap();
    ///
    /// assert_eq!(get_value(&arr, &"1".to_string()), Some(&"1".to_owned()));
    /// assert_eq!(get_value_borrow_key(&arr, &"5".to_string()), Some(&"5".to_owned()));
    /// assert_eq!(get_value_borrow_key(&arr, "8"), Some(&"8".to_owned()));
    /// ```
    fn get_value(&self, key: &E) -> Option<&Self::Value>;

    /// Returns a converted value corresponding to the given key.
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
    /// use std::collections::HashMap;
    /// use collection_traits::AnyCollectionRef;
    /// use std::borrow::Cow;
    ///
    /// let mut map1 = HashMap::new();
    /// map1.insert(1, "a".to_owned());
    /// assert_eq!(map1.get_converted::<Cow<_>>(&1), Some(Cow::from("a")));
    /// assert_eq!(map1.get_converted::<Cow<_>>(&2), None);
    ///
    /// let mut map2 = HashMap::new();
    /// map2.insert(2, "b".to_owned());
    ///
    /// let arr = [map1, map2];
    /// assert_eq!(arr.get_converted::<Cow<_>>(&1), Some(Cow::from("a")));
    /// assert_eq!(arr.get_converted::<Cow<_>>(&2), Some(Cow::from("b")));
    /// assert_eq!(arr.get_converted::<Cow<_>>(&3), None);
    ///
    /// // When key and value are the same
    /// let vec = vec!["a".to_owned(), "b".into(), "c".into()];
    /// assert_eq!(vec.get_converted::<Cow<_>>("a"), Some(Cow::from("a")));
    /// ```
    fn get_converted<'a, 'b, FV>(&'a self, key: &E) -> Option<FV>
    where
        FV: From<&'b Self::Value>,
        Self::Value: 'b,
        'a: 'b,
    {
        if let Some(value) = self.get_value(key) {
            return Some(value.into());
        }
        None
    }

    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a Self::Key`.
    ///
    /// # Note
    ///
    /// 1. Note that the key and value can be the same value (for example,
    /// if the container is a Vec<_>)! So the iterator returned by this
    /// method can be the same iterator as that returned by
    /// [`AnyCollectionRef::collection_values()`].
    ///
    /// 2. The implementation of the iterator depends on the container type,
    /// so iteration over the keys can take as `O(capacity)` so as `O(len)`
    /// time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    ///
    /// let map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);
    ///
    /// // Unfortunately, when calling AnyCollectionRef methods directly,
    /// // you need to specify the type E
    /// let mut keys = AnyCollectionRef::<i32>::collection_keys(&map1).collect::<Vec<_>>();
    /// keys.sort_unstable();
    /// assert_eq!(keys, [&1, &2, &3]);
    ///
    /// let map2: HashMap<i32, i32> = HashMap::from([(4, 40), (5, 50), (6, 60)]);
    ///
    /// // But you do not need to specify the type E when using AnyCollectionRef
    /// // as trait bound
    /// fn get_all_keys<T: AnyCollectionRef>(container: &T) -> Vec<&T::Key> {
    ///     container.collection_keys().collect::<Vec<_>>()
    /// }
    ///
    /// let mut keys = get_all_keys(&map1);
    /// keys.sort_unstable();
    /// assert_eq!(keys, [&1, &2, &3]);
    ///
    /// let mut keys = get_all_keys(&map2);
    /// keys.sort_unstable();
    /// assert_eq!(keys, [&4, &5, &6]);
    ///
    /// let arr = (0..3)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)))
    ///     .try_collect_collections_array::<[Vec<_>; 3]>()
    ///     .unwrap();
    ///
    /// let keys = get_all_keys(&arr);
    /// assert_eq!(keys, [&0, &1, &2, &3, &4, &5, &6, &7, &8]);
    /// ```
    fn collection_keys(&self) -> Self::Keys<'_>;

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a Self::Value`.
    ///
    /// # Note
    ///
    /// 1. Note that the key and value can be the same value (for example,
    /// if the container is a Vec<_>)! So the iterator returned by this
    /// method can be the same iterator as that returned by
    /// [`AnyCollectionRef::collection_keys()`].
    ///
    /// 2. The implementation of the iterator depends on the container type,
    /// so iteration over the keys can take as `O(capacity)` so as `O(len)`
    /// time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{AnyCollectionRef, TryCollectArray};
    /// use hashbrown::HashMap;
    ///
    /// let map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);
    ///
    /// // Unfortunately, when calling AnyCollectionRef methods directly,
    /// // you need to specify the type E
    /// let mut values = AnyCollectionRef::<i32>::collection_values(&map1).collect::<Vec<_>>();
    /// values.sort_unstable();
    /// assert_eq!(values, [&10, &20, &30]);
    ///
    /// let map2: HashMap<i32, i32> = HashMap::from([(4, 40), (5, 50), (6, 60)]);
    ///
    /// // But you do not need to specify the type E when using AnyCollectionRef
    /// // as trait bound
    /// fn get_all_values<T: AnyCollectionRef>(container: &T) -> Vec<&T::Value> {
    ///     container.collection_values().collect::<Vec<_>>()
    /// }
    ///
    /// let mut values = get_all_values(&map1);
    /// values.sort_unstable();
    /// assert_eq!(values, [&10, &20, &30]);
    ///
    /// let mut values = get_all_values(&map2);
    /// values.sort_unstable();
    /// assert_eq!(values, [&40, &50, &60]);
    ///
    /// let arr = (0..3)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)))
    ///     .try_collect_collections_array::<[Vec<_>; 3]>()
    ///     .unwrap();
    ///
    /// let values = get_all_values(&arr);
    /// assert_eq!(values, [&0, &1, &2, &3, &4, &5, &6, &7, &8]);
    /// ```
    fn collection_values(&self) -> Self::Values<'_>;
}

impl<T, E: ?Sized> AnyCollectionRef<E> for &T
where
    T: ?Sized + AnyCollectionRef<E>,
{
    type Keys<'a> = T::Keys<'a>
    where
        Self: 'a,
        Self::Key: 'a;

    type Values<'a> = T::Values<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        <T as AnyCollectionRef<E>>::collection_len(self)
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        <T as AnyCollectionRef<E>>::is_collection_empty(self)
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        <T as AnyCollectionRef<E>>::contains_eq(self, key)
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        <T as AnyCollectionRef<E>>::get_value(self, key)
    }

    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        <T as AnyCollectionRef<E>>::collection_keys(self)
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        <T as AnyCollectionRef<E>>::collection_values(self)
    }
}

impl<T, E: ?Sized> AnyCollectionRef<E> for &mut T
where
    T: ?Sized + AnyCollectionRef<E>,
{
    type Keys<'a> = T::Keys<'a>
    where
        Self: 'a,
        Self::Key: 'a;

    type Values<'a> = T::Values<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        <T as AnyCollectionRef<E>>::collection_len(self)
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        <T as AnyCollectionRef<E>>::is_collection_empty(self)
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        <T as AnyCollectionRef<E>>::contains_eq(self, key)
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        <T as AnyCollectionRef<E>>::get_value(self, key)
    }

    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        <T as AnyCollectionRef<E>>::collection_keys(self)
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        <T as AnyCollectionRef<E>>::collection_values(self)
    }
}

macro_rules! impl_any_container_ref_for_vec_type {
    (impl for $type_n:ty, T $(: $bound:ident)?, Key = $key:ty,
        Value = $value:ty, Iters = $iter:ty) => (
            impl<T, E> AnyCollectionRef<E> for $type_n
            where
                $(T: $bound,)?
                E: ?Sized + Equivalent<T>,
            {
                type Keys<'a> = $iter where Self:'a, T: 'a;
                type Values<'a> = $iter where Self:'a, T: 'a;

                #[inline]
                fn collection_len(&self) -> usize {
                    self.len()
                }

                #[inline]
                fn is_collection_empty(&self) -> bool {
                    self.is_empty()
                }

                #[inline]
                fn contains_eq(&self, key: &E) -> bool {
                    self.iter().any(|x| Equivalent::equivalent(key, x))
                }

                #[inline]
                fn get_value(&self, key: &E) -> Option<&Self::Value> {
                    self.iter().find(|x| Equivalent::equivalent(key, *x))
                }

                #[inline]
                fn collection_keys(&self) -> Self::Keys<'_> {
                    self.iter()
                }

                #[inline]
                fn collection_values(&self) -> Self::Values<'_> {
                    self.iter()
                }
            }
        );
}

impl_any_container_ref_for_vec_type! {
    impl for [T], T, Key = T, Value = T, Iters = core::slice::Iter<'a, T>
}

impl_any_container_ref_for_vec_type! {
    impl for Vec<T>, T, Key = T, Value = T, Iters = core::slice::Iter<'a, T>
}

impl_any_container_ref_for_vec_type! {
    impl for im::Vector<T>, T: Clone, Key = T, Value = T,
    Iters = im::vector::Iter<'a, T>
}

impl_any_container_ref_for_vec_type! {
    impl for collections::VecDeque<T>, T, Key = T, Value = T,
    Iters = vec_deque::Iter<'a, T>
}

impl_any_container_ref_for_vec_type! {
    impl for collections::LinkedList<T>, T, Key = T, Value = T,
    Iters = linked_list::Iter<'a, T>
}

impl_any_container_ref_for_vec_type! {
    impl for collections::BinaryHeap<T>, T, Key = T, Value = T,
    Iters = binary_heap::Iter<'a, T>
}

impl<T, A, E> AnyCollectionRef<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    type Keys<'a> = slice::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a> = slice::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        self.iter().any(|x| Equivalent::equivalent(key, x))
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        self.iter().find(|x| Equivalent::equivalent(key, *x))
    }

    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<K, V, Q, S> AnyCollectionRef<Q> for collections::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Keys<'a>  = hash_map::Keys<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = hash_map::Values<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<K, V, Q, S> AnyCollectionRef<Q> for hashbrown::HashMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type Keys<'a>  = hashbrown::hash_map::Keys<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = hashbrown::hash_map::Values<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<K, V, Q, S> AnyCollectionRef<Q> for im::HashMap<K, V, S>
where
    K: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Keys<'a>  = im::hashmap::Keys<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = im::hashmap::Values<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<K, V, Q, S> AnyCollectionRef<Q> for indexmap::IndexMap<K, V, S>
where
    K: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<K>,
    S: BuildHasher,
{
    type Keys<'a>  = indexmap::map::Keys<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = indexmap::map::Values<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<K, V, Q> AnyCollectionRef<Q> for collections::BTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Keys<'a>  = btree_map::Keys<'a, K, V>  where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = btree_map::Values<'a, K, V>  where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<K, V, Q> AnyCollectionRef<Q> for im::OrdMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Keys<'a>  = im::ordmap::Keys<'a, K, V> where Self: 'a, K: 'a, V: 'a;
    type Values<'a>  = im::ordmap::Values<'a, K, V> where Self: 'a, K: 'a, V: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains_key(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.keys()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.values()
    }
}

impl<T, Q, S> AnyCollectionRef<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Keys<'a>  = hash_set::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a>  = hash_set::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> AnyCollectionRef<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type Keys<'a>  = hashbrown::hash_set::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a>  = hashbrown::hash_set::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> AnyCollectionRef<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type Keys<'a>  = indexmap::set::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a>  = indexmap::set::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> AnyCollectionRef<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Keys<'a> = im::hashset::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a> = im::hashset::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, key: &Q) -> bool {
        self.contains(key)
    }

    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        if self.contains(key) {
            return self.iter().find(|x| Equivalent::equivalent(key, *x));
        }
        None
    }

    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q> AnyCollectionRef<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Keys<'a>  = btree_set::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a>  = btree_set::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, eq: &Q) -> bool {
        self.contains(eq)
    }
    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        self.get(key)
    }
    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }
    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q> AnyCollectionRef<Q> for im::OrdSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Keys<'a> = im::ordset::Iter<'a, T> where Self: 'a, T: 'a;
    type Values<'a> = im::ordset::Iter<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.len()
    }
    #[inline]
    fn is_collection_empty(&self) -> bool {
        self.is_empty()
    }
    #[inline]
    fn contains_eq(&self, key: &Q) -> bool {
        self.contains(key)
    }

    #[inline]
    fn get_value(&self, key: &Q) -> Option<&Self::Value> {
        if self.contains(key) {
            return self.iter().find(|x| Equivalent::equivalent(key, *x));
        }
        None
    }

    #[inline]
    fn collection_keys(&self) -> Self::Keys<'_> {
        self.iter()
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<E, T, const N: usize> AnyCollectionRef<E> for [T; N]
where
    E: ?Sized,
    T: AnyCollectionRef<E>,
{
    type Keys<'a> = FlatMap<slice::Iter<'a, T>, T::Keys<'a>, fn(&'a T) -> T::Keys<'a>>
    where
        Self: 'a,
        Self::Key: 'a;

    type Values<'a> = FlatMap<slice::Iter<'a, T>, T::Values<'a>, fn(&'a T) -> T::Values<'a>>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        self.iter().map(|x| x.collection_len()).sum()
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        <[T; N] as AnyCollectionRef<E>>::collection_len(self) == 0
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        self.iter().any(|x| x.contains_eq(key))
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        if let Some(container) = self.iter().find(|x| x.contains_eq(key)) {
            return container.get_value(key);
        }
        None
    }

    #[inline]
    fn collection_keys<'a>(&'a self) -> Self::Keys<'a> {
        #[inline(always)]
        fn keys_iter<E1, T1>(item: &T1) -> T1::Keys<'_>
        where
            E1: ?Sized,
            T1: AnyCollectionRef<E1>,
        {
            item.collection_keys()
        }
        self.iter().flat_map(keys_iter as fn(&'a T) -> T::Keys<'a>)
    }

    #[inline]
    fn collection_values<'a>(&'a self) -> Self::Values<'a> {
        #[inline(always)]
        fn values_iter<E1, T1>(item: &T1) -> T1::Values<'_>
        where
            E1: ?Sized,
            T1: AnyCollectionRef<E1>,
        {
            item.collection_values()
        }
        self.iter()
            .flat_map(values_iter as fn(&'a T) -> T::Values<'a>)
    }
}
