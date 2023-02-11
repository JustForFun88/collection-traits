use super::{Equivalent, ValueContain};
use core::borrow::Borrow;
use core::hash::BuildHasher;
use core::hash::Hash;
use core::iter::FlatMap;
use core::slice;
use smallvec::SmallVec;
use std::collections::{self, binary_heap, btree_set, hash_set, linked_list, vec_deque};

/// A trait that allows you to abstract from various types of collections /
/// containers that can have some value stored inside.
///
/// Provides a basic API that allows you to work with both the owning or
/// reference variable.
///
/// # Note
///
/// This trait does not guarantee:
///
/// 1. Does not guarantee that the value is unique and does not repeat
/// inside the container.
///
/// 2. Does not guarantee that this is a single container `T` or an array
/// of containers `[T; N]` where `T: ValueContainerRef`.
///
/// When implementing this trait, you need to be careful about the type `E`
/// of the  lookup key. For greater flexibility, there are no restrictions
/// on the type of search key, but one of two conditions must be met:
///
/// 1. If it is possible to implement it, then it is desirable to specify
///    the condition `E: Equivalent<Self::Value>`.
/// 2. If the first condition cannot be met (e.g. for [`std::collections::HashSet`]),
///    the key **must be** any borrowed form of the container's key type (i.e.
///    `Self::Value: Borrow<E>` ) .
///
/// Note that a container that implements `E: Equivalent<Self::Value>` will also
/// accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but the reverse
/// is not true.
pub trait ValueCollectionRef<E = <Self as ValueContain>::Value>
where
    Self: ValueContain,
    E: ?Sized,
{
    /// The type of the iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a Self::Value`.
    ///
    /// It is created by the [`ValueCollectionRef::collection_values()`].
    /// See its documentation for more.
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
    /// container. For example, for `a = [T; N]` where `T: ValueCollectionRef`,
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
    /// use collection_traits::{ValueCollectionRef, TryCollectArray};
    /// use hashbrown::HashSet;
    ///
    /// let mut map1: HashSet<String> = HashSet::new();
    ///
    /// // Unfortunately, when calling ValueCollectionRef methods directly,
    /// // you need to specify the type E
    /// assert_eq!(ValueCollectionRef::<String>::collection_len(&map1), 0);
    /// assert_eq!(ValueCollectionRef::<str>::collection_len(&map1), 0);
    ///
    /// map1.insert("a".to_owned());
    ///
    /// let map2: HashSet<usize> = HashSet::from([1, 2]);
    ///
    /// // But you do not need to specify the type E when using ValueCollectionRef
    /// // as trait bound
    /// fn get_len<T: ValueCollectionRef>(container: &T) -> usize {
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
    /// // Array::len and ValueCollectionRef::collection_len are not the same value
    /// assert_eq!(arr.len(), 3);
    /// assert_eq!(get_len(&arr), 9);
    /// ```
    fn collection_len(&self) -> usize;

    /// Returns `true` if the container contains no `V: Value` elements.
    ///
    /// # Note
    ///
    /// Note that this does not mean that the container is actually empty.
    /// For example, for `a = [T; N]` where `T: ValueCollectionRef`, `a.len() = N`,
    /// but `a.is_collection_empty() = <[T; N] as ValueCollectionRef<E>>::collection_len(self) == 0`.
    ///
    /// You will also have to specify the type `E` when calling this method if
    /// the compiler cannot infer this from the context. This usually happens
    /// when you call the given method directly on the object, rather than
    /// behind a generic inside a function (see examples below).
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{ValueCollectionRef, TryCollectArray};
    /// use hashbrown::HashSet;
    ///
    /// let mut map1: HashSet<String> = HashSet::new();
    ///
    /// // Unfortunately, when calling ValueCollectionRef methods directly,
    /// // you need to specify the type E
    /// assert!(ValueCollectionRef::<String>::is_collection_empty(&map1));
    /// assert!(ValueCollectionRef::<str>::is_collection_empty(&map1));
    ///
    /// map1.insert("a".to_owned());
    ///
    /// let map2: HashSet<usize> = HashSet::from([1, 2]);
    ///
    /// // But you do not need to specify the type E when using ValueCollectionRef
    /// // as trait bound
    /// fn is_collection_empty<T: ValueCollectionRef>(container: &T) -> bool {
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
    /// // Array::len and ValueCollectionRef::collection_len are not the same value
    /// assert!(!arr.is_empty());
    /// assert!(is_collection_empty(&arr));
    /// ```
    fn is_collection_empty(&self) -> bool;

    /// Returns `true` if the container contains a value for the
    /// specified key.
    ///
    /// # Note
    ///
    /// Note that this trait does not guarantee that the returned value is
    /// unique and does not repeat within the container.
    ///
    /// The lookup key `E` must be either a borrowed form of the container's
    /// key type (ie `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{ValueCollectionRef, TryCollectArray};
    /// use hashbrown::HashSet;
    /// use core::borrow::Borrow;
    ///
    /// let map1: HashSet<String> = HashSet::from(["a".into(), "b".into()]);
    ///
    /// // You do not need to specify the type E when calling this `ValueCollectionRef`
    /// // method directly.
    /// assert!(map1.contains_eq(&"a".to_string()));
    /// assert!(map1.contains_eq("b"));
    ///
    /// // Also, there is no need to specify the type E when using ValueCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn contain_value<T>(cont: &T, key: &T::Value) -> bool
    /// where
    ///     T: ValueCollectionRef + ?Sized,
    /// {
    ///     cont.contains_eq(key)
    /// }
    ///
    /// fn contain_borrow_value<T, Q: ?Sized>(cont: &T, key: &Q) -> bool
    /// where
    ///     T: ValueCollectionRef<Q> + ?Sized,
    ///     T::Value: Borrow<Q>,
    /// {
    ///     cont.contains_eq(key)
    /// }
    ///
    /// assert!(contain_value(&map1, &"a".to_string()));
    /// // assert!(contain_value(&map1, "a")); // Err: expected struct `String`, found `str`
    ///
    /// assert!(contain_borrow_value(&map1, &"a".to_string()));
    /// assert!(contain_borrow_value(&map1, "a"));
    ///
    /// let arr = (0..3)
    ///     .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
    ///     .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
    ///     .unwrap();
    ///
    /// assert!(contain_value(&arr, &"1".to_string()));
    /// assert!(contain_borrow_value(&arr, &"5".to_string()));
    /// assert!(contain_borrow_value(&arr, "8"));
    /// ```    
    fn contains_eq(&self, key: &E) -> bool;

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Note
    ///
    /// Note that this trait does not guarantee that the returned value is
    /// unique and does not repeat within the container.
    ///
    /// The lookup key `E` must be either a borrowed form of the container's
    /// key type (ie `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{ValueCollectionRef, TryCollectArray};
    /// use hashbrown::HashSet;
    /// use core::borrow::Borrow;
    ///
    /// let map1: HashSet<String> = HashSet::from(["a".into(), "b".into()]);
    ///
    /// // You do not need to specify the type E when calling this `ValueCollectionRef`
    /// // method directly.
    /// assert_eq!(map1.get_value(&"a".to_string()), Some(&"a".to_string()));
    /// assert_eq!(map1.get_value("b"), Some(&"b".to_string()));
    ///
    /// // Also, there is no need to specify the type E when using ValueCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn get_value<'a, 'b, T>(cont: &'a T, key: &'b T::Value) -> Option<&'a T::Value>
    /// where
    ///     T: ValueCollectionRef + ?Sized,
    /// {
    ///     cont.get_value(key)
    /// }
    ///
    /// fn get_value_borrow_key<'a, 'b, T, Q: ?Sized>(cont: &'a T, key: &'b Q) -> Option<&'a T::Value>
    /// where
    ///     T: ValueCollectionRef<Q> + ?Sized,
    ///     T::Value: Borrow<Q>,
    /// {
    ///     cont.get_value(key)
    /// }
    ///
    /// assert_eq!(get_value(&map1, &"a".to_string()), Some(&"a".to_string()));
    /// // assert_eq!(get_value(&map1, "a"), Some(&1)); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(get_value_borrow_key(&map1, &"a".to_string()), Some(&"a".to_string()));
    /// assert_eq!(get_value_borrow_key(&map1, "a"), Some(&"a".to_string()));
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
    /// Note that this trait does not guarantee that the returned value is
    /// unique and does not repeat within the container.
    ///
    /// The lookup key `E` must be either a borrowed form of the container's
    /// key type (ie `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use collection_traits::ValueCollectionRef;
    /// use std::borrow::Cow;
    ///
    /// let mut map1 = HashSet::new();
    /// map1.insert("a".to_owned());
    /// assert_eq!(map1.get_converted::<Cow<_>>("a"), Some(Cow::from("a")));
    /// assert_eq!(map1.get_converted::<Cow<_>>("b"), None);
    ///
    /// let mut map2 = HashSet::new();
    /// map2.insert("b".to_owned());
    ///
    /// let arr = [map1, map2];
    /// assert_eq!(arr.get_converted::<Cow<_>>("a"), Some(Cow::from("a")));
    /// assert_eq!(arr.get_converted::<Cow<_>>("b"), Some(Cow::from("b")));
    /// assert_eq!(arr.get_converted::<Cow<_>>("c"), None);
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

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a Self::Value`.
    ///
    /// # Note
    ///
    /// The implementation of the iterator depends on the container type,
    /// so iteration over the keys can take as `O(capacity)` so as `O(len)`
    /// time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::{ValueCollectionRef, TryCollectArray};
    /// use hashbrown::HashSet;
    ///
    /// let map1: HashSet<i32> = HashSet::from([1, 2, 3]);
    ///
    /// // Unfortunately, when calling ValueCollectionRef methods directly,
    /// // you need to specify the type E
    /// let mut values = ValueCollectionRef::<i32>::collection_values(&map1).collect::<Vec<_>>();
    /// values.sort_unstable();
    /// assert_eq!(values, [&1, &2, &3]);
    ///
    /// let map2: HashSet<i32> = HashSet::from([4, 5, 6]);
    ///
    /// // But you do not need to specify the type E when using ValueCollectionRef
    /// // as trait bound
    /// fn get_all_values<T: ValueCollectionRef>(container: &T) -> Vec<&T::Value> {
    ///     container.collection_values().collect::<Vec<_>>()
    /// }
    ///
    /// let mut values = get_all_values(&map1);
    /// values.sort_unstable();
    /// assert_eq!(values, [&1, &2, &3]);
    ///
    /// let mut values = get_all_values(&map2);
    /// values.sort_unstable();
    /// assert_eq!(values, [&4, &5, &6]);
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

impl<T, E: ?Sized> ValueCollectionRef<E> for &T
where
    T: ValueCollectionRef<E>,
{
    type Values<'a> = T::Values<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        <T as ValueCollectionRef<E>>::collection_len(self)
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        <T as ValueCollectionRef<E>>::is_collection_empty(self)
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        <T as ValueCollectionRef<E>>::contains_eq(self, key)
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        <T as ValueCollectionRef<E>>::get_value(self, key)
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        <T as ValueCollectionRef<E>>::collection_values(self)
    }
}

impl<T, E: ?Sized> ValueCollectionRef<E> for &mut T
where
    T: ValueCollectionRef<E>,
{
    type Values<'a> = T::Values<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_len(&self) -> usize {
        <T as ValueCollectionRef<E>>::collection_len(self)
    }

    #[inline]
    fn is_collection_empty(&self) -> bool {
        <T as ValueCollectionRef<E>>::is_collection_empty(self)
    }

    #[inline]
    fn contains_eq(&self, key: &E) -> bool {
        <T as ValueCollectionRef<E>>::contains_eq(self, key)
    }

    #[inline]
    fn get_value(&self, key: &E) -> Option<&Self::Value> {
        <T as ValueCollectionRef<E>>::get_value(self, key)
    }

    #[inline]
    fn collection_values(&self) -> Self::Values<'_> {
        <T as ValueCollectionRef<E>>::collection_values(self)
    }
}

macro_rules! impl_value_container_ref_for_vec_type {
    (impl for $type_n:ty, T $(: $bound:ident)?, Value = $key:ty,
        Value = $value:ty, Iters = $iter:ty) => (
            impl<T, E> ValueCollectionRef<E> for $type_n
            where
                $(T: $bound,)?
                E: ?Sized + Equivalent<T>,
            {
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
                fn collection_values(&self) -> Self::Values<'_> {
                    self.iter()
                }
            }
        );
}

impl_value_container_ref_for_vec_type! {
    impl for [T], T, Value = T, Value = T, Iters = core::slice::Iter<'a, T>
}

impl_value_container_ref_for_vec_type! {
    impl for Vec<T>, T, Value = T, Value = T, Iters = core::slice::Iter<'a, T>
}

impl_value_container_ref_for_vec_type! {
    impl for im::Vector<T>, T: Clone, Value = T, Value = T,
    Iters = im::vector::Iter<'a, T>
}

impl_value_container_ref_for_vec_type! {
    impl for collections::VecDeque<T>, T, Value = T, Value = T,
    Iters = vec_deque::Iter<'a, T>
}

impl_value_container_ref_for_vec_type! {
    impl for collections::LinkedList<T>, T, Value = T, Value = T,
    Iters = linked_list::Iter<'a, T>
}

impl_value_container_ref_for_vec_type! {
    impl for collections::BinaryHeap<T>, T, Value = T, Value = T,
    Iters = binary_heap::Iter<'a, T>
}

impl<T, A, E> ValueCollectionRef<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> ValueCollectionRef<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> ValueCollectionRef<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> ValueCollectionRef<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q, S> ValueCollectionRef<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q> ValueCollectionRef<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<T, Q> ValueCollectionRef<Q> for im::OrdSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
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
    fn collection_values(&self) -> Self::Values<'_> {
        self.iter()
    }
}

impl<E, T, const N: usize> ValueCollectionRef<E> for [T; N]
where
    E: ?Sized,
    T: ValueCollectionRef<E>,
{
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
        <[T; N] as ValueCollectionRef<E>>::collection_len(self) == 0
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
    fn collection_values<'a>(&'a self) -> Self::Values<'a> {
        #[inline(always)]
        fn values_iter<E1, T1>(item: &T1) -> T1::Values<'_>
        where
            E1: ?Sized,
            T1: ValueCollectionRef<E1>,
        {
            item.collection_values()
        }
        self.iter()
            .flat_map(values_iter as fn(&'a T) -> T::Values<'a>)
    }
}
