use super::{Equivalent, SetCollectionRef, ValueCollectionRef, ValueContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections;

/// A trait that allows you to abstract from various types of set
/// collections.
///
/// Provides an API that allows you to add and remove elements, and perform
/// other operations on a set.
///
/// # Note
///
/// Note that this trait guarantees that all values are unique and do not
/// repeat within the container.
///
/// To prevent this invariant from being violated, the implementation of
/// this trait outside of this crate is prohibited (via [`SetCollectionRef`]).
//
// # Notes about the implementation of the trait within this crate
//
// When implementing this trait, you need to be careful about the type `E`
// of the  lookup value. For greater flexibility, there are no restrictions
// on the type of search value, but one of two conditions must be met:
//
// 1. If it is possible to implement it, then it is desirable to specify
//    the condition `E: Equivalent<Self::Value>`.
// 2. If the first condition cannot be met (e.g. for [`std::collections::HashSet`]),
//    the value **must be** any borrowed form of the container's value type (i.e.
//    `Self::Value: Borrow<E>` ) .
//
// Note that a container that implements `E: Equivalent<Self::Value>` will also
// accept all `E` lookup values such as `Self::Value: Borrow<E>`, but the reverse
// is not true.
pub trait SetCollectionMut<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + SetCollectionRef<E>,
    E: ?Sized,
{
    /// Adds a value to the set. If the set did not have this value
    /// present, `true` is returned. If the set did have this value
    /// present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use hashbrown::HashSet;
    /// use std::rc::Rc;
    ///
    /// let mut set = HashSet::new();
    ///
    /// // Unfortunately, when calling SetCollectionMut
    /// // methods directly, you need to specify the type E
    /// assert_eq!(
    ///     SetCollectionMut::<i32>::collection_insert(&mut set, Rc::new(2)),
    ///     true
    /// );
    ///
    /// // But you do not need to specify the type E when using SetCollectionMut
    /// // as trait bound
    /// fn insert<T: SetCollectionMut>(set_1: &mut T, value: T::Value) -> bool {
    ///     set_1.collection_insert(value)
    /// }
    ///
    /// let value = Rc::new(3);
    /// assert_eq!(insert(&mut set, value.clone()), true);
    /// assert_eq!(insert(&mut set, Rc::new(3)), false);
    /// assert!(set.len() == 2 && Rc::strong_count(&value) == 2);
    ///
    /// let mut set = im::HashSet::new();
    ///
    /// let value = Rc::new(1);
    /// assert_eq!(insert(&mut set, value.clone()), true);
    /// assert_eq!(insert(&mut set, Rc::new(1)), false);
    /// assert!(set.len() == 1 && Rc::strong_count(&value) == 2);
    /// ```
    fn collection_insert(&mut self, value: Self::Value) -> bool;

    /// Removes a value from the set. Returns whether the value was
    /// present in the set.
    ///
    /// # Note
    ///
    /// Note that this trait guarantees that returned values are unique and not
    /// repeated within the container.
    ///
    /// The lookup value `E` must be either a borrowed form of the container's
    /// value type (i.e. `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup values such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::Value` collection may need to
    /// implement the [`Hash`] and [`Eq`] or [`Ord`] traits. Thus, the corresponding
    /// search value `E` must also implement the corresponding traits.
    ///
    /// If the required traits are [`Hash`] and [`Eq`] then `Hash` and `Eq` on the
    /// lookup value must match those for the value type.
    ///
    /// If the required trait is [`Ord`] than the ordering on the lookup value must
    /// match the ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use core::borrow::Borrow;
    /// use hashbrown::HashSet;
    ///
    /// let mut set: HashSet<_> = HashSet::from(["a", "b", "c", "d"].map(ToOwned::to_owned));
    ///
    /// // You do not need to specify the type E when calling this `ValueCollectionRef`
    /// // method directly.
    /// assert!(set.collection_remove("d"));
    ///
    /// // Also, there is no need to specify the type E when using ValueCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn remove<T>(collection: &mut T, value: &T::Value) -> bool
    /// where
    ///     T: SetCollectionMut + ?Sized,
    /// {
    ///     collection.collection_remove(value)
    /// }
    ///
    /// fn remove_borrow_value<T, Q: ?Sized>(collection: &mut T, value: &Q) -> bool
    /// where
    ///     T: SetCollectionMut<Q> + ?Sized,
    ///     T::Value: Borrow<Q>,
    /// {
    ///     collection.collection_remove(value)
    /// }
    ///
    /// assert!(!remove(&mut set, &"d".to_owned()));
    ///
    /// // assert!(remove(&mut set, "a")); // Err: expected struct `String`, found `str`
    ///
    /// assert!(remove_borrow_value(&mut set, &"b".to_string()));
    /// assert!(remove_borrow_value(&mut set, "c"));
    /// ```
    fn collection_remove(&mut self, value: &E) -> bool;

    /// Removes and returns the value in the set, if any, that is equal
    /// to the given one.
    ///
    /// # Note
    ///
    /// Note that this trait guarantees that returned values are unique and not
    /// repeated within the container.
    ///
    /// The lookup value `E` must be either a borrowed form of the container's
    /// value type (i.e. `Self::Value: Borrow<E>`) or, if implemented for this
    /// container, `E: Equivalent<Self::Value>`.
    ///
    /// Note that a container that implements `E: Equivalent<Self::Value>` will
    /// also accept all `E` lookup values such as `Self::Value: Borrow<E>`, but
    /// the converse is not true.
    ///
    /// Depending on the collection type, the `Self::Value` collection may need to
    /// implement the [`Hash`] and [`Eq`] or [`Ord`] traits. Thus, the corresponding
    /// search value `E` must also implement the corresponding traits.
    ///
    /// If the required traits are [`Hash`] and [`Eq`] then `Hash` and `Eq` on the
    /// lookup value must match those for the value type.
    ///
    /// If the required trait is [`Ord`] than the ordering on the lookup value must
    /// match the ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use core::borrow::Borrow;
    /// use hashbrown::HashSet;
    ///
    /// let mut set: HashSet<_> = HashSet::from(["a", "b", "c", "d"].map(ToOwned::to_owned));
    ///
    /// // You do not need to specify the type E when calling this `ValueCollectionRef`
    /// // method directly.
    /// assert_eq!(set.collection_take("d"), Some("d".to_owned()));
    ///
    /// // Also, there is no need to specify the type E when using ValueCollectionRef
    /// // as a trait bound (although specifying it will give more flexibility).
    /// fn take<T>(collection: &mut T, value: &T::Value) -> Option<T::Value>
    /// where
    ///     T: SetCollectionMut + ?Sized,
    /// {
    ///     collection.collection_take(value)
    /// }
    ///
    /// fn take_borrow_value<T, Q: ?Sized>(collection: &mut T, value: &Q) -> Option<T::Value>
    /// where
    ///     T: SetCollectionMut<Q> + ?Sized,
    ///     T::Value: Borrow<Q>,
    /// {
    ///     collection.collection_take(value)
    /// }
    ///
    /// assert_eq!(take(&mut set, &"d".to_owned()), None);
    ///
    /// // assert_eq!(take(&mut set, "a"), Some("a".to_owned())); // Err: expected struct `String`, found `str`
    ///
    /// assert_eq!(
    ///     take_borrow_value(&mut set, &"b".to_string()),
    ///     Some("b".to_owned())
    /// );
    /// assert_eq!(take_borrow_value(&mut set, "c"), Some("c".to_owned()));
    /// ```
    fn collection_take(&mut self, value: &E) -> Option<Self::Value>;

    /// Adds a value to the set, replacing the existing value, if any,
    /// that is equal to the given one. Returns the replaced value.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use hashbrown::HashSet;
    /// use std::rc::Rc;
    ///
    /// let array = [1, 2, 3].map(Rc::new);
    /// let mut set: HashSet<_> = HashSet::from_iter(array.iter().map(Clone::clone));
    ///
    /// assert!(array.iter().all(|x| Rc::strong_count(x) == 2));
    /// // Unfortunately, when calling SetCollectionMu
    /// // methods directly, you need to specify the type E
    /// assert_eq!(
    ///     SetCollectionMut::<i32>::collection_replace(&mut set, Rc::new(1)),
    ///     Some(Rc::new(1))
    /// );
    ///
    /// // But you do not need to specify the type E when using SetCollectionMut
    /// // as trait bound
    /// fn replace<T: SetCollectionMut>(set_1: &mut T, value: T::Value) -> Option<T::Value> {
    ///     set_1.collection_replace(value)
    /// }
    ///
    /// assert_eq!(replace(&mut set, Rc::new(2)), Some(Rc::new(2)));
    /// assert_eq!(replace(&mut set, Rc::new(3)), Some(Rc::new(3)));
    ///
    /// assert!(array.iter().all(|x| Rc::strong_count(x) == 1));
    ///
    /// let mut set: im::HashSet<_> = im::HashSet::from_iter(array.iter().map(Clone::clone));
    ///
    /// assert!(array.iter().all(|x| Rc::strong_count(x) == 2));
    ///
    /// assert_eq!(replace(&mut set, Rc::new(1)), Some(Rc::new(1)));
    /// assert_eq!(replace(&mut set, Rc::new(2)), Some(Rc::new(2)));
    /// assert_eq!(replace(&mut set, Rc::new(3)), Some(Rc::new(3)));
    ///
    /// assert!(set.len() == 3 && array.iter().all(|x| Rc::strong_count(x) == 1));
    /// ```
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value>;

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use hashbrown::HashSet;
    /// use std::collections::BTreeSet;
    ///
    /// let mut set = HashSet::new();
    ///
    /// set.insert("a".to_owned());
    /// assert!(!set.is_empty());
    /// // Unfortunately, when calling SetCollectionMut methods directly,
    /// // you need to specify the type E
    /// SetCollectionMut::<str>::collection_clear(&mut set);
    /// assert!(set.is_empty());
    ///
    /// // But you do not need to specify the type E when using SetCollectionMut
    /// // as trait bound.
    /// fn clear<T: SetCollectionMut>(collection: &mut T) {
    ///     collection.collection_clear();
    /// }
    ///
    /// let mut set = HashSet::from(["a".to_owned(), "b".into()]);
    /// clear(&mut set);
    /// assert!(set.is_empty());
    ///
    /// let mut set = BTreeSet::from([("a".to_owned(), 1), ("b".into(), 2)]);
    /// clear(&mut set);
    /// assert!(set.is_empty());
    /// ```
    fn collection_clear(&mut self);

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `Self::Value` such
    /// that `f(&Self::Value)` returns `false`. The elements are
    /// visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionMut;
    /// use hashbrown::HashSet;
    /// use std::collections::BTreeSet;
    ///
    /// let mut set: HashSet<i32> = (0..8).collect();
    /// assert_eq!(set.len(), 8);
    ///
    /// // Unfortunately, when calling SetCollectionMut methods directly,
    /// // you need to specify the type E
    /// SetCollectionMut::<i32>::collection_retain(&mut set, |&v| v % 2 == 0);
    ///
    /// // We can see, that the number of elements inside set is changed.
    /// assert_eq!(set.len(), 4);
    ///
    /// let mut vec: Vec<i32> = set.iter().cloned().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [0, 2, 4, 6]);
    ///
    /// // But you do not need to specify the type E when using SetCollectionMut
    /// // as trait bound.
    /// fn retain<T: SetCollectionMut, F>(collection: &mut T, f: F)
    /// where
    ///     F: FnMut(&T::Value) -> bool,
    /// {
    ///     collection.collection_retain(f);
    /// }
    ///
    /// let mut set: HashSet<i32> = (0..8).collect();
    /// retain(&mut set, |&v| v % 2 == 0);
    ///
    /// let mut vec: Vec<i32> = set.iter().cloned().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [0, 2, 4, 6]);
    ///
    /// let mut set: BTreeSet<i32> = (0..8).collect();
    /// retain(&mut set, |&v| v % 2 == 0);
    ///
    /// let mut vec: Vec<i32> = set.iter().cloned().collect();
    /// vec.sort_unstable();
    /// assert_eq!(vec, [0, 2, 4, 6]);
    /// ```
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;
}

impl<T, E> SetCollectionMut<E> for &mut T
where
    E: ?Sized,
    T: SetCollectionMut<E>,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        <T as SetCollectionMut<E>>::collection_insert(self, value)
    }

    #[inline]
    fn collection_remove(&mut self, value: &E) -> bool {
        <T as SetCollectionMut<E>>::collection_remove(self, value)
    }

    #[inline]
    fn collection_take(&mut self, value: &E) -> Option<Self::Value> {
        <T as SetCollectionMut<E>>::collection_take(self, value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        <T as SetCollectionMut<E>>::collection_replace(self, value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        <T as SetCollectionMut<E>>::collection_clear(self)
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        <T as SetCollectionMut<E>>::collection_retain(self, f)
    }
}

impl<T, Q, S> SetCollectionMut<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value)
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.take(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q, S> SetCollectionMut<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value)
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.take(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q, S> SetCollectionMut<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value)
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.take(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T: Clone, Q, S> SetCollectionMut<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        if !self.contains(value.borrow()) {
            im::HashSet::insert(self, value);
            return true;
        }
        false
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value).is_some()
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.remove(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.insert(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q> SetCollectionMut<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value)
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.take(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T: Clone, Q> SetCollectionMut<Q> for im::OrdSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    #[inline]
    fn collection_insert(&mut self, value: Self::Value) -> bool {
        if !self.contains(value.borrow()) {
            im::OrdSet::insert(self, value);
            return true;
        }
        false
    }

    #[inline]
    fn collection_remove(&mut self, value: &Q) -> bool {
        self.remove(value).is_some()
    }

    #[inline]
    fn collection_take(&mut self, value: &Q) -> Option<Self::Value> {
        self.remove(value)
    }

    #[inline]
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.insert(value)
    }

    #[inline]
    fn collection_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn collection_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        let values = self.iter().cloned().collect::<Vec<_>>();
        for value in values {
            if !f(&value) {
                self.remove(value.borrow());
            }
        }
    }
}
