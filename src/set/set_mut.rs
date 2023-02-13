use super::{Equivalent, SetCollectionRef, ValueCollectionRef, ValueContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections;

/// A trait that allows you to abstract from various types of set
/// collections.
///
/// Provides an API that allows you to add and remove elements, and perform
/// other operations on a table.
///
/// # Note
///
/// Note that this trait guarantees that all values are unique and do not
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
//    the condition `E: Equivalent<Self::Value>`.
// 2. If the first condition cannot be met (e.g. for [`std::collections::HashSet`]),
//    the key **must be** any borrowed form of the container's key type (i.e.
//    `Self::Value: Borrow<E>` ) .
//
// Note that a container that implements `E: Equivalent<Self::Value>` will also
// accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but the reverse
// is not true.
pub trait SetCollectionMut<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + SetCollectionRef<E>,
    E: ?Sized,
{
    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
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
    /// use crate::SetCollectionMut;
    /// use hashbrown::HashSet;
    ///
    /// let mut set: HashSet<_> = ["a", "b", "c", "d"]
    ///     .map(ToOwned::to_owned)
    ///     .into_iter()
    ///     .collect();
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
    fn collection_remove(&mut self, key: &E) -> bool;
    fn collection_take(&mut self, key: &E) -> Option<Self::Value>;
    fn collection_replace(&mut self, value: Self::Value) -> Option<Self::Value>;
    fn collection_clear(&mut self);
    fn collection_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;
}

#[test]
fn test() {
    use crate::SetCollectionMut;
    use hashbrown::HashSet;

    let mut set: HashSet<_> = ["a", "b", "c", "d"]
        .map(ToOwned::to_owned)
        .into_iter()
        .collect();

    // You do not need to specify the type E when calling this `ValueCollectionRef`
    // method directly.
    assert!(set.collection_remove("d"));

    // Also, there is no need to specify the type E when using ValueCollectionRef
    // as a trait bound (although specifying it will give more flexibility).
    fn remove<T>(collection: &mut T, value: &T::Value) -> bool
    where
        T: SetCollectionMut + ?Sized,
    {
        collection.collection_remove(value)
    }

    fn remove_borrow_value<T, Q: ?Sized>(collection: &mut T, value: &Q) -> bool
    where
        T: SetCollectionMut<Q> + ?Sized,
        T::Value: Borrow<Q>,
    {
        collection.collection_remove(value)
    }

    assert!(!remove(&mut set, &"d".to_owned()));

    // assert!(remove(&mut set, "a")); // Err: expected struct `String`, found `str`

    assert!(remove_borrow_value(&mut set, &"b".to_string()));
    assert!(remove_borrow_value(&mut set, "c"));
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
    fn collection_remove(&mut self, key: &E) -> bool {
        <T as SetCollectionMut<E>>::collection_remove(self, key)
    }

    #[inline]
    fn collection_take(&mut self, key: &E) -> Option<Self::Value> {
        <T as SetCollectionMut<E>>::collection_take(self, key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key).is_some()
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
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
    fn collection_remove(&mut self, key: &Q) -> bool {
        self.remove(key).is_some()
    }

    #[inline]
    fn collection_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
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
